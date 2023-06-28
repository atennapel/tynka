package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*
import Locals.*
import common.Debug.debug

import scala.annotation.tailrec
import scala.collection.immutable.IntMap
import scala.util.{Failure, Success, Try}

object Unification:
  case class UnifyError(msg: String) extends Exception(msg)

  private final case class PSub(
      occ: Option[MetaId],
      dom: Lvl,
      cod: Lvl,
      sub: IntMap[Val]
  ):
    def lift: PSub = PSub(occ, dom + 1, cod + 1, sub + (cod.expose, VVar(dom)))
    def skip: PSub = PSub(occ, dom, cod + 1, sub)

  private def invert(sp: Spine)(implicit gamma: Lvl): (PSub, Option[Pruning]) =
    def go(sp: Spine): (Lvl, Set[Lvl], IntMap[Val], Pruning, Boolean) = sp match
      case SId => (lvl0, Set.empty, IntMap.empty, Nil, true)
      case SApp(f, a, i) =>
        val (dom, domvars, sub, pr, isLinear) = go(f)
        def invertVal(
            x: Lvl,
            invx: Val
        ): (Lvl, Set[Lvl], IntMap[Val], Pruning, Boolean) =
          if domvars.contains(x) then
            (dom + 1, domvars, sub - x.expose, None :: pr, false)
          else
            (
              dom + 1,
              domvars + x,
              sub + (x.expose -> invx),
              Some(i) :: pr,
              isLinear
            )
        force(a) match
          case VVar(x)         => invertVal(x, VVar(dom))
          case VQuote(VVar(x)) => invertVal(x, VRigid(HVar(dom), SSplice(SId)))
          case VRigid(HVar(x), SSplice(SId)) => invertVal(x, VQuote(VVar(dom)))
          case _ => throw UnifyError(s"non-var in meta spine")
      case _ => throw UnifyError(s"non-app in meta spine")
    val (dom, _, sub, pr, isLinear) = go(sp)
    (PSub(None, dom, gamma, sub), if isLinear then None else Some(pr))

  private def pruneTy(p: RevPruning, a: VTy): Ty =
    def go(p: Pruning, a: VTy)(implicit psub: PSub): Ty = (p, force(a)) match
      case (Nil, a) => psubst(a)
      case (Some(_) :: p, VPi(x, i, a, b)) =>
        Pi(x, i, psubst(a), go(p, b(VVar(psub.cod)))(psub.lift))
      case (None :: p, VPi(_, _, _, b)) => go(p, b(VVar(psub.cod)))(psub.skip)
      case _                            => impossible()
    go(p.expose, a)(PSub(None, lvl0, lvl0, IntMap.empty))

  private def pruneMeta(p: Pruning, m: MetaId): Val =
    val u = getMetaUnsolved(m)
    val mty = u.ty
    val prunedty = eval(pruneTy(revPruning(p), mty))(Nil)
    val m2 = freshMeta(prunedty, u.stage)
    val solution = eval(lams(mkLvl(p.size), mty, AppPruning(Meta(m2), p)))(Nil)
    solveMeta(m, solution)
    solution

  private def etaExpandMeta(m: MetaId): Val =
    val uns = getMetaUnsolved(m)
    val a = uns.ty
    def go(a: VTy, s: VStage, lvl: Lvl, p: Pruning, locals: Locals): Tm =
      force(a) match
        case VPi(x, i, a, b) =>
          Lam(
            x,
            i,
            quote(a)(lvl),
            go(
              b(VVar(lvl)),
              s,
              lvl + 1,
              Some(Expl) :: p,
              Bound(locals, x, quote(a)(lvl), s.map(vf => quote(vf)(lvl)))
            )
          )
        case VLift(vf, a) => go(a, STy(vf), lvl, p, locals).quote
        case a =>
          val closed = eval(locals.closeTy(quote(a)(lvl)))(Nil)
          val m = freshMeta(closed, s)
          AppPruning(Meta(m), p)
    val t = go(a, SMeta, lvl0, Nil, Empty)
    val v = eval(t)(Nil)
    solveMeta(m, v)
    v

  @tailrec
  private def hasSplice(sp: Spine): Boolean = sp match
    case SId            => false
    case SApp(sp, _, _) => hasSplice(sp)
    case SSplice(_)     => true
    case _              => impossible()

  private def expandVFlex(m: MetaId, sp: Spine): (MetaId, Spine) =
    if !hasSplice(sp) then (m, sp)
    else
      val m2 = etaExpandMeta(m)
      val VFlex(mx, spx) = vspine(m2, sp): @unchecked
      (mx, spx)

  private def pruneVFlex(m0: MetaId, sp0: Spine)(implicit
      psub: PSub
  ): (MetaId, Spine) =
    val (m, sp) = expandVFlex(m0, sp0)
    def pruning(sp: Spine): Option[Pruning] = sp match
      case SId => Some(Nil)
      case SApp(sp, t, i) =>
        pruning(sp).flatMap { p =>
          def varCase(x: Lvl): Option[Pruning] = psub.sub.get(x.expose) match
            case Some(_) => Some(Some(i) :: p)
            case None    => Some(None :: p)
          force(t) match
            case VVar(x)                       => varCase(x)
            case VRigid(HVar(x), SSplice(SId)) => varCase(x)
            case VQuote(VVar(x))               => varCase(x)
            case _                             => None
        }
      case _ => None
    pruning(sp) match
      case Some(p) if p.exists(_.isEmpty) =>
        val m2 = pruneMeta(p, m)
        val VFlex(mx, spx) = vspine(m2, sp): @unchecked
        (mx, spx)
      case _ => (m, sp)

  private def splitSpine(sp: Spine): (Spine, Spine) =
    def or(
        a: Option[(Spine, Spine)],
        b: Option[(Spine, Spine)]
    ): Option[(Spine, Spine)] =
      a.fold(b)(_ => a)
    def go(sp: Spine): Option[(Spine, Spine)] = sp match
      case SId           => None
      case SApp(f, a, i) => go(f).map((l, r) => (l, SApp(r, a, i)))
      case SSplice(t)    => go(t).map((l, r) => (l, SSplice(r)))
      case SProj(sp, p) =>
        or(go(sp), Some((sp, SId))).map((l, r) => (l, SProj(r, p)))
      case SPrim(sp, x, args) =>
        or(go(sp), Some((sp, SId))).map((l, r) => (l, SPrim(r, x, args)))
    go(sp).fold((sp, SId))(x => x)

  private def psubst(v: Val)(implicit psub: PSub): Tm =
    def goSp(t: Tm, sp: Spine)(implicit psub: PSub): Tm = sp match
      case SId              => t
      case SApp(fn, arg, i) => App(goSp(t, fn), go(arg), i)
      case SSplice(sp)      => goSp(t, sp).splice
      case SProj(hd, proj)  => Proj(goSp(t, hd), proj, Irrelevant, Irrelevant)
      case SPrim(sp, x, args) =>
        val as = args.foldLeft(Prim(x)) { case (f, (a, i)) => App(f, go(a), i) }
        App(as, goSp(t, sp), Expl)
    def go(v: Val)(implicit psub: PSub): Tm = force(v, UnfoldMetas) match
      case VRigid(HVar(x), sp) =>
        psub.sub.get(x.expose) match
          case None    => throw UnifyError(s"escaping variable '$x")
          case Some(w) => goSp(quote(w)(psub.dom), sp)
      case VRigid(HPrim(x), sp) => goSp(Prim(x), sp)
      case VU(s)                => U(s.map(go))

      case VFlex(m, _) if psub.occ.contains(m) =>
        throw UnifyError(s"occurs check failed ?$m")
      case VFlex(m0, sp0) =>
        val (inner, outer) = splitSpine(sp0)
        val (m, sp) = pruneVFlex(m0, inner)
        val inner2 = goSp(Meta(m), sp)
        goSp(inner2, outer)

      case VGlobal(x, sp, _) => goSp(Global(x), sp)

      case VPi(x, i, t, b) => Pi(x, i, go(t), go(b(VVar(psub.cod)))(psub.lift))
      case VLam(x, i, ty, b) =>
        Lam(x, i, go(ty), go(b(VVar(psub.cod)))(psub.lift))

      case VSigma(x, t, b) => Sigma(x, go(t), go(b(VVar(psub.cod)))(psub.lift))
      case VPair(fst, snd, t) => Pair(go(fst), go(snd), go(t))

      case VLift(vf, t) => Lift(go(vf), go(t))
      case VQuote(t)    => go(t).quote

      case VIrrelevant => Irrelevant
    go(v)

  private def lams(l: Lvl, a: VTy, t: Tm): Tm =
    def go(a: VTy, l2: Lvl): Tm =
      if l2 == l then t
      else
        force(a) match
          case VPi(x, i, _, b) =>
            val y = x match
              case DontBind => DoBind(Name(s"x$l2"))
              case _        => x
            Lam(y, i, quote(a)(l2), go(b(VVar(l2)), l2 + 1))
          case _ => impossible()
    go(a, lvl0)

  private def solve(m: MetaId, topSp: Spine, topRhs: Val)(implicit
      l: Lvl
  ): Unit =
    debug(s"solve ?$m := ${quote(topRhs)}")
    val (sp, outer) = splitSpine(topSp)
    val (m2, sp2) = expandVFlex(m, sp)
    val psub = invert(sp2)
    if outer.isEmpty then solveWithPSub(m2, psub, topRhs)
    else
      force(topRhs) match
        case VRigid(x, rhsSp) =>
          @tailrec
          def goProj(a: Spine, b: Spine, n: Int)(implicit l: Lvl): Unit =
            (a, n) match
              case (a, 0)             => go(a, b)
              case (SProj(a, Snd), n) => goProj(a, b, n - 1)
              case _ =>
                throw UnifyError(s"solve ?$m2, spine projection mismatch")
          def go(a: Spine, b: Spine): Unit = (a, b) match
            case (SId, b) => solveWithPSub(m2, psub, VRigid(x, b))
            case (SApp(s1, a, _), SApp(s2, b, _)) => go(s1, s2); unify(a, b)
            case (SSplice(s1), SSplice(s2))       => go(s1, s2)
            case (SProj(s1, p1), SProj(s2, p2)) if p1 == p2 => go(s1, s2)
            case (SProj(s1, Fst), SProj(s2, Named(_, n)))   => goProj(s1, s2, n)
            case (SProj(s1, Named(_, n)), SProj(s2, Fst))   => goProj(s1, s2, n)
            case (SPrim(a, x, as1), SPrim(b, y, as2)) if x == y =>
              go(a, b)
              as1.zip(as2).foreach { case ((v, _), (w, _)) => unify(v, w) }
            case _ => throw UnifyError(s"solve ?$m2, spine mismatch")
          go(outer, rhsSp)
        case _ => throw UnifyError(s"solve ?$m2, invalid spine")

  private def solveWithPSub(
      m: MetaId,
      data: (PSub, Option[Pruning]),
      rhs: Val
  ): Unit =
    val (psub, pruneNonLinear) = data
    val mty = getMetaUnsolved(m).ty
    pruneNonLinear.foreach(pr => pruneTy(revPruning(pr), mty))
    val rhs2 = psubst(rhs)(psub.copy(occ = Some(m)))
    val solution = lams(psub.dom, mty, rhs2)
    debug(s"solution ?$m = $solution")
    solveMeta(m, eval(solution)(Nil))

  private def flexFlex(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine)(implicit
      gamma: Lvl
  ): Unit =
    Try {
      val (spn, outer) = splitSpine(sp)
      if !outer.isEmpty then throw UnifyError(s"flex flex ?$m, invalid spine")
      val (m2, spx) = expandVFlex(m, spn)
      val psub = invert(spx)
      (m2, spx, psub)
    } match
      case Success((m, sp, psub)) => solveWithPSub(m, psub, VFlex(m2, sp2))
      case Failure(_: UnifyError) => solve(m2, sp2, VFlex(m, sp))
      case Failure(err)           => throw err

  private def intersect(m: MetaId, sp0: Spine, sp02: Spine)(implicit
      l: Lvl
  ): Unit =
    val (sp, outer) = splitSpine(sp0)
    val (sp2, outer2) = splitSpine(sp02)
    if outer.isEmpty && outer2.isEmpty then
      val (m2, sp3) = expandVFlex(m, sp)
      val VFlex(_, sp4) = force(VFlex(m, sp2)): @unchecked
      def go(a: Spine, b: Spine): Option[Pruning] = (a, b) match
        case (SId, SId) => Some(Nil)
        case (SApp(a, v, i), SApp(b, w, _)) =>
          (force(v), force(w)) match
            case (VVar(x), VVar(x2)) =>
              go(a, b).map(p => (if x == x2 then Some(i) else None) :: p)
            case (VQuote(VVar(x)), VQuote(VVar(x2))) =>
              go(a, b).map(p => (if x == x2 then Some(i) else None) :: p)
            case (
                  VRigid(HVar(x), SSplice(SId)),
                  VRigid(HVar(x2), SSplice(SId))
                ) =>
              go(a, b).map(p => (if x == x2 then Some(i) else None) :: p)
            case _ => None
        case _ => impossible()
      go(sp3, sp4) match
        case None                        => unify(sp3, sp4)
        case Some(p) if p.contains(None) => pruneMeta(p, m2)
        case _                           => ()
    else unify(sp, sp2)

  @tailrec
  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit l: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError(s"spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit l: Lvl): Unit = (a, b) match
    case (SId, SId)                       => ()
    case (SApp(s1, a, _), SApp(s2, b, _)) => unify(s1, s2); unify(a, b)
    case (SSplice(s1), SSplice(s2))       => unify(s1, s2)
    case (SProj(s1, p1), SProj(s2, p2)) if p1 == p2 => unify(s1, s2)
    case (SProj(s1, Fst), SProj(s2, Named(_, n)))   => unifyProj(s1, s2, n)
    case (SProj(s1, Named(_, n)), SProj(s2, Fst))   => unifyProj(s1, s2, n)
    case (SPrim(a, x, as1), SPrim(b, y, as2)) if x == y =>
      unify(a, b)
      as1.zip(as2).foreach { case ((v, _), (w, _)) => unify(v, w) }
    case _ => throw UnifyError(s"spine mismatch")

  private def unify(a: Clos, b: Clos)(implicit l: Lvl): Unit =
    val v = VVar(l)
    unify(a(v), b(v))(l + 1)

  def unify(a: VStage, b: VStage)(implicit l: Lvl): Unit = (a, b) match
    case (SMeta, SMeta)   => ()
    case (STy(a), STy(b)) => unify(a, b)
    case _ =>
      throw UnifyError(s"cannot unify ${quoteS(a)} ~ ${quoteS(b)}")

  def unify(a: Val, b: Val)(implicit l: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a, UnfoldMetas), force(b, UnfoldMetas)) match
      case (VU(s1), VU(s2)) => unify(s1, s2)
      case (VPi(_, i1, a1, b1), VPi(_, i2, a2, b2)) if i1 == i2 =>
        unify(a1, a2); unify(b1, b2)
      case (VSigma(_, a1, b1), VSigma(_, a2, b2)) =>
        unify(a1, a2); unify(b1, b2)
      case (VLam(_, _, _, b1), VLam(_, _, _, b2)) => unify(b1, b2)
      case (VPair(a1, b1, _), VPair(a2, b2, _)) => unify(a1, a2); unify(b1, b2)
      case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)
      case (VLift(vf1, ty1), VLift(vf2, ty2)) =>
        unify(vf1, vf2); unify(ty1, ty2)
      case (VQuote(a), VQuote(b)) => unify(a, b)
      case (VIrrelevant, _)       => ()
      case (_, VIrrelevant)       => ()

      case (VFlex(m, sp), VFlex(m2, sp2)) =>
        if m == m2 then intersect(m, sp, sp2) else flexFlex(m, sp, m2, sp2)

      case (VLam(_, i, _, b), w) =>
        val v = VVar(l); unify(b(v), vapp(w, v, i))(l + 1)
      case (w, VLam(_, i, _, b)) =>
        val v = VVar(l); unify(vapp(w, v, i), b(v))(l + 1)
      case (VPair(a, b, _), w) => unify(a, vfst(w)); unify(b, vsnd(w))
      case (w, VPair(a, b, _)) => unify(vfst(w), a); unify(vsnd(w), b)

      case (VFlex(m, sp), v) => solve(m, sp, v)
      case (v, VFlex(m, sp)) => solve(m, sp, v)

      case (VUnit(), _) => ()
      case (_, VUnit()) => ()

      case (VGlobal(x1, sp1, v1), VGlobal(x2, sp2, v2)) if x1 == x2 =>
        try unify(sp1, sp2)
        catch case _: UnifyError => unify(v1(), v2())
      case (VGlobal(_, _, v), VGlobal(_, _, w)) => unify(v(), w())
      case (VGlobal(_, _, v), w)                => unify(v(), w)
      case (w, VGlobal(_, _, v))                => unify(w, v())

      case (_, _) => throw UnifyError(s"cannot unify ${quote(a)} ~ ${quote(b)}")
