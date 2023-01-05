package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*
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

  private def pruneMeta(p: Pruning, m: MetaId): MetaId =
    val u = getMetaUnsolved(m)
    val mty = u.ty
    val prunedty = eval(pruneTy(revPruning(p), mty))(Nil)
    val m2 = freshMeta(prunedty, u.univ)
    val solution = eval(lams(mkLvl(p.size), mty, AppPruning(Meta(m2), p)))(Nil)
    solveMeta(m, solution)
    m2

  /*
  etaExpandMeta :: MetaVar -> IO Val
  etaExpandMeta m = do
    (!a, !s) <- readUnsolved m

    let go :: Cxt -> VTy -> Stage -> IO Tm
        go cxt a s = case force a of
          VPi x i a b -> Lam x i (quote (lvl cxt) a) <$!> go (bind cxt x a s) (b $ VVar (lvl cxt)) s
                                                    <*!> pure V0
          VLift a     -> Quote <$!> go cxt a S0
          a           -> freshMeta cxt a s

    t <- go (emptyCxt (initialPos "")) a s
    let val = eval [] t
    modifyIORef' mcxt $ IM.insert (coerce m) (Solved val a s)
    pure val
   */

  private def etaExpandMeta(m: MetaId): Val =
    val uns = getMetaUnsolved(m)
    val a = uns.ty
    val s = uns.univ
    def go(a: VTy, u: VUniv)(implicit ctx: Ctx): Tm = ???
    val t = go(a, s)(Ctx.empty((0, 0)))
    val v = eval(t)(Nil)
    solveMeta(m, v)
    v

  private enum PruneStatus:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import PruneStatus.*

  private def pruneVFlex(m: MetaId, sp: Spine)(implicit psub: PSub): Tm =
    def go(sp: Spine): (List[(Option[Tm], Icit)], PruneStatus) = sp match
      case SId => (Nil, OKRenaming)
      case SApp(sp, t, i) =>
        val (sp2, status) = go(sp)
        force(t) match
          case VVar(x) =>
            (psub.sub.get(x.expose), status) match
              case (Some(x), _) =>
                ((Some(Var(x.toIx(psub.dom))), i) :: sp2, status)
              case (None, OKNonRenaming) =>
                throw UnifyError(s"meta prune failure ?$m")
              case (None, _) => ((None, i) :: sp2, NeedsPruning)
          case t =>
            status match
              case NeedsPruning => throw UnifyError(s"meta prune failure ?$m")
              case _            => ((Some(psubst(t)), i) :: sp2, OKNonRenaming)
      case _ => throw UnifyError(s"non-app in meta spine of ?$m")
    val (sp2, status) = go(sp)
    val m2 = status match
      case NeedsPruning => pruneMeta(sp2.map((m, i) => m.map(_ => i)), m)
      case _            => getMetaUnsolved(m); m
    sp2.foldRight(Meta(m2)) { case ((m, i), t) => m.fold(t)(App(t, _, i)) }

  private def psubst(v: Val)(implicit psub: PSub): Tm =
    def goSp(t: Tm, sp: Spine)(implicit psub: PSub): Tm = sp match
      case SId              => t
      case SApp(fn, arg, i) => App(goSp(t, fn), go(arg), i)
      case SProj(hd, proj)  => Proj(goSp(t, hd), proj)
      case SPrim(sp, x, args) =>
        val as = args.foldLeft(Prim(x)) { case (f, (a, i)) => App(f, go(a), i) }
        App(as, goSp(t, sp), Expl)
    def go(v: Val)(implicit psub: PSub): Tm = force(v, UnfoldMetas) match
      case VRigid(HVar(x), sp) =>
        psub.sub.get(x.expose) match
          case None    => throw UnifyError(s"escaping variable '$x")
          case Some(w) => goSp(quote(w)(psub.dom), sp)
      case VRigid(HPrim(x), sp) => goSp(Prim(x), sp)

      case VFlex(m, _) if psub.occ.contains(m) =>
        throw UnifyError(s"occurs check failed ?$m")
      case VFlex(m, sp) => pruneVFlex(m, sp)

      case VGlobal(x, sp, _) => goSp(Global(x), sp)

      case VPi(x, i, t, b) => Pi(x, i, go(t), go(b(VVar(psub.cod)))(psub.lift))
      case VLam(x, i, b)   => Lam(x, i, go(b(VVar(psub.cod)))(psub.lift))

      case VSigma(x, t, b) => Sigma(x, go(t), go(b(VVar(psub.cod)))(psub.lift))
      case VPair(fst, snd) => Pair(go(fst), go(snd))
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
            Lam(y, i, go(b(VVar(l2)), l2 + 1))
          case _ => impossible()
    go(a, lvl0)

  private def solve(m: MetaId, sp: Spine, rhs: Val)(implicit l: Lvl): Unit =
    debug(s"solve ?$m := ${quote(rhs)}")
    solveWithPRen(m, invert(sp), rhs)

  private def solveWithPRen(
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
    def go(m: MetaId, sp: Spine, m2: MetaId, sp2: Spine): Unit =
      Try(invert(sp)) match
        case Success(pren)          => solveWithPRen(m, pren, VFlex(m2, sp2))
        case Failure(_: UnifyError) => solve(m2, sp2, VFlex(m, sp))
        case Failure(err)           => throw err
    if sp.size < sp2.size then go(m2, sp2, m, sp) else go(m, sp, m2, sp2)

  private def intersect(m: MetaId, sp: Spine, sp2: Spine)(implicit
      l: Lvl
  ): Unit =
    def go(sp: Spine, sp2: Spine): Option[Pruning] = (sp, sp2) match
      case (SId, SId) => Some(Nil)
      case (SApp(sp, t, i), SApp(sp2, t2, _)) =>
        (force(t), force(t2)) match
          case (VVar(x), VVar(x2)) =>
            go(sp, sp2).map(pr => (if x == x2 then Some(i) else None) :: pr)
          case _ => None
      case _ => None
    go(sp, sp2) match
      case None                          => unify(sp, sp2)
      case Some(pr) if pr.contains(None) => pruneMeta(pr, m)
      case _                             => ()

  @tailrec
  private def unifyProj(a: Spine, b: Spine, n: Int)(implicit l: Lvl): Unit =
    (a, n) match
      case (a, 0)             => unify(a, b)
      case (SProj(a, Snd), n) => unifyProj(a, b, n - 1)
      case _                  => throw UnifyError(s"spine projection mismatch")

  private def unify(a: Spine, b: Spine)(implicit l: Lvl): Unit = (a, b) match
    case (SId, SId)                       => ()
    case (SApp(s1, a, _), SApp(s2, b, _)) => unify(s1, s2); unify(a, b)
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

  def unify(a: Val, b: Val)(implicit l: Lvl): Unit =
    debug(s"unify ${quote(a)} ~ ${quote(b)}")
    (force(a, UnfoldMetas), force(b, UnfoldMetas)) match
      case (VPi(_, i1, a1, b1), VPi(_, i2, a2, b2)) if i1 == i2 =>
        unify(a1, a2); unify(b1, b2)
      case (VSigma(_, a1, b1), VSigma(_, a2, b2)) =>
        unify(a1, a2); unify(b1, b2)
      case (VLam(_, _, b1), VLam(_, _, b2)) => unify(b1, b2)
      case (VPair(a1, b1), VPair(a2, b2))   => unify(a1, a2); unify(b1, b2)
      case (VRigid(h1, s1), VRigid(h2, s2)) if h1 == h2 => unify(s1, s2)

      case (VFlex(m, sp), VFlex(m2, sp2)) =>
        if m == m2 then intersect(m, sp, sp2) else flexFlex(m, sp, m2, sp2)

      case (VLam(_, i, b), w) =>
        val v = VVar(l); unify(b(v), vapp(w, v, i))(l + 1)
      case (w, VLam(_, i, b)) =>
        val v = VVar(l); unify(vapp(w, v, i), b(v))(l + 1)
      case (VPair(a, b), w) => unify(a, vfst(w)); unify(b, vsnd(w))
      case (w, VPair(a, b)) => unify(vfst(w), a); unify(vsnd(w), b)

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
