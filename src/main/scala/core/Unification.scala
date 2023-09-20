package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*
import common.Debug.debug

import scala.annotation.tailrec
import scala.collection.immutable.IntMap

object Unification:
  case class UnifyError(msg: String) extends Exception(msg)

  // partial substitution
  private enum PSEntry:
    case PSNonLinear
    case PS0(value: Val0)
    case PS1(value: Val1)
  import PSEntry.*

  private final case class PSub(
      occ: Option[MetaId],
      dom: Lvl,
      cod: Lvl,
      sub: IntMap[PSEntry],
      isLinear: Boolean
  ):
    def lift1: PSub =
      PSub(
        occ,
        dom + 1,
        cod + 1,
        sub + (cod.expose -> PS1(VVar1(dom))),
        isLinear
      )
    def lift0: PSub =
      PSub(
        occ,
        dom + 1,
        cod + 1,
        sub + (cod.expose -> PS0(VVar0(dom))),
        isLinear
      )
    inline def skip: PSub = copy(cod = cod + 1)

  private object PSub:
    val empty = PSub(None, lvl0, lvl0, IntMap.empty, true)

  // fresh metas
  @tailrec
  private def closeType(ls: Locals, xs: List[Bind], top: Ty): Ty =
    (ls, xs) match
      case (LEmpty, Nil) => top
      case (LDef(ls, ty, v), DoBind(x) :: xs) =>
        closeType(ls, xs, Let1(x, ty, v, top))
      case (LBind0(ls, ty, cv), x :: xs) =>
        closeType(ls, xs, Pi(x, Expl, Lift(cv, ty), top))
      case (LBind1(ls, ty), x :: xs) =>
        closeType(ls, xs, Pi(x, Expl, ty, top))
      case _ => impossible()

  def freshMeta(ty: VTy)(implicit ctx: Ctx): Tm1 =
    val lvl = ctx.lvl
    val qa = closeType(ctx.locals, ctx.binds, quote1(ty, LiftVars(lvl))(lvl))
    val id = newMeta(eval1(qa)(EEmpty))
    AppPruning(Meta(id), ???)

  inline def freshCV()(implicit ctx: Ctx): CV = freshMeta(VCV1)

  // inversion
  private def invertVal1(v: Val1, rhs: Val1)(implicit psub: PSub): PSub =
    forceAll1(v) match
      case VVar1(x) =>
        val sub = psub.sub
        if sub.contains(x.expose) then
          psub.copy(isLinear = false, sub = sub + (x.expose -> PSNonLinear))
        else psub.copy(sub = sub + (x.expose -> PS1(rhs)))
      case VQuote(v) => invertVal0(v, vsplice(rhs))
      case _         => throw UnifyError("non-var in spine")

  private def invertVal0(v: Val0, rhs: Val0)(implicit psub: PSub): PSub =
    forceAll0(v) match
      case VVar0(x) =>
        val sub = psub.sub
        if sub.contains(x.expose) then
          psub.copy(isLinear = false, sub = sub + (x.expose -> PSNonLinear))
        else psub.copy(sub = sub + (x.expose -> PS0(rhs)))
      case VSplice(v) => invertVal1(v, vquote(rhs))
      case _          => throw UnifyError("non-var in spine")

  private def invert(sp: Spine)(implicit lvl: Lvl): PSub = sp match
    case SId => PSub.empty
    case SApp(sp, v, i) =>
      val psub = invert(sp)
      val d = psub.dom
      invertVal1(v, VVar1(d))(psub.copy(dom = d + 1))

  // expansion
  private def metaEtaExpansion(id: MetaId, sp: Spine): Val1 =
    def go(ctx: Ctx, sp: Spine, ty: Val1): Tm1 = (sp, forceAll1(ty)) match
      case (SId, ty) => freshMeta(ty)(ctx)
      case (SApp(sp, arg, i), VPi(x, _, a, b)) =>
        val qa = quote1(a, UnfoldNone)(ctx.lvl)
        Lam1(x, i, qa, go(ctx.bind1(x, qa, a), sp, b(VVar1(ctx.lvl))))
      case _ => impossible()
    eval1(go(Ctx.empty, sp.reverse, unsolvedMetaType(id)))(EEmpty)

  private def expandMeta(ctx: Ctx, id: MetaId, sp: Spine): Val1 =
    val v = metaEtaExpansion(id, sp)
    solveWithPSub(id, SId, v)(PSub.empty)
    vspine(v, sp)

  private def validateRhsType(mty: VTy, sp: Spine)(implicit psub: PSub): Unit =
    def getTy(ty: VTy, sp: Spine): VTy = (ty, sp) match
      case (ty, SId)                           => ty
      case (VPi(x, i, a, b), SApp(sp, arg, _)) => getTy(b(arg), sp)
      case _                                   => impossible()
    psubst1(getTy(mty, sp.reverse))
    ()

  private def pruneTy(p: RevPruning, ty: VTy): Ty =
    def go(p: Pruning, psub: PSub, ty: VTy): Ty = (p, forceAll1(ty)) match
      case (Nil, ty) => psubst1(ty)(psub)
      case (PESkip :: p, VPi(x, i, a, b)) =>
        go(p, psub.skip, b(VVar1(psub.cod)))
      case (PEBind1(_) :: p, VPi(x, i, a, b)) =>
        Pi(x, i, psubst1(a)(psub), go(p, psub.lift1, b(VVar1(psub.cod))))
      case _ => impossible()
    go(p.expose, PSub.empty, ty)

  // substitution
  private def psubst0(v: Val0)(implicit psub: PSub): Tm0 =
    inline def go0(v: Val0) = psubst0(v)
    inline def go1(v: Val1) = psubst1(v)
    inline def goClos(c: Clos[Tm0]) = psubst0(c.dive(psub.cod))(psub.lift0)
    forceMetas0(v) match
      case VVar0(x) =>
        psub.sub.get(x.expose) match
          case None              => throw UnifyError(s"out of scope $x")
          case Some(PS1(_))      => impossible()
          case Some(PS0(v))      => quote0(v, UnfoldNone)(psub.dom)
          case Some(PSNonLinear) => throw UnifyError(s"non-linear")
      case VLet0(x, ty, v, b) => Let0(x, go1(ty), go0(v), goClos(b))
      case VLam0(x, ty, b)    => Lam0(x, go1(ty), goClos(b))
      case VApp0(f, a)        => App0(go0(f), go0(a))
      case VSplice(v)         => Splice(go1(v))

  private def psubstSp(h: Tm1, sp: Spine)(implicit psub: PSub): Tm1 = sp match
    case SId            => h
    case SApp(sp, v, i) => App1(psubstSp(h, sp), psubst1(v), i)

  private def psubst1(v: Val1)(implicit psub: PSub): Tm1 =
    inline def go0(v: Val0) = psubst0(v)
    inline def go1(v: Val1) = psubst1(v)
    inline def goSp(h: Tm1, sp: Spine) = psubstSp(h, sp)
    inline def goClos(c: Clos[Tm1]) = psubst1(c(VVar1(psub.cod)))(psub.lift1)
    forceMetas1(v) match
      case VRigid(x, sp) =>
        psub.sub.get(x.expose) match
          case None              => throw UnifyError(s"out of scope $x")
          case Some(PS0(_))      => impossible()
          case Some(PS1(v))      => goSp(quote1(v, UnfoldNone)(psub.dom), sp)
          case Some(PSNonLinear) => throw UnifyError("non-linear")
      case VFlex(id, sp) =>
        if psub.occ.contains(id) then throw UnifyError(s"occurs error ?$id")
        else goSp(Meta(id), sp)
      case VUnfold(_, _, v)   => psubst1(v())
      case VPi(x, i, ty, b)   => Pi(x, i, go1(ty), goClos(b))
      case VLam1(x, i, ty, b) => Lam1(x, i, go1(ty), goClos(b))
      case VU0(cv)            => U0(go1(cv))
      case VU1                => U1
      case VFun(pty, cv, rty) => Fun(go1(pty), go1(cv), go1(rty))
      case VCV1               => CV1
      case VComp              => Comp
      case VVal               => Val
      case VLift(cv, ty)      => Lift(go1(cv), go1(ty))
      case VQuote(tm)         => Quote(go0(tm))

  // solving
  private def lams(ty: VTy, b: Tm1)(implicit lvl: Lvl): Tm1 =
    def go(l1: Lvl, l2: Lvl, ty: VTy, b: Tm1): Tm1 =
      if l1 == l2 then b
      else
        forceAll1(ty) match
          case VPi(x, i, a, c) =>
            Lam1(
              x,
              i,
              quote1(a, UnfoldNone)(l2),
              go(l1, l2 + 1, c(VVar1(l2)), b)
            )
          case _ => impossible()
    go(lvl, lvl0, ty, b)

  private def solve(id: MetaId, sp: Spine, rhs: Val1)(implicit lvl: Lvl): Unit =
    val ty = unsolvedMetaType(id)
    implicit val psub = invert(sp)(lvl)
    solveWithPSub(id, sp, rhs)

  private def solveWithPSub(id: MetaId, sp: Spine, rhs: Val1)(implicit
      psub: PSub
  ) =
    val ty = unsolvedMetaType(id)
    val qrhs = {
      if !psub.isLinear then validateRhsType(ty, sp)
      psubst1(rhs)(psub.copy(occ = Some(id)))
    }
    val sol = eval1(lams(ty, qrhs)(psub.dom))(EEmpty)
    solveMeta(id, sol, Set.empty) // TODO: meta dependencies

  // unification
  def unify0(a: Val0, b: Val0)(implicit lvl: Lvl): Unit =
    inline def goClos(a: Clos[Tm0], b: Clos[Tm0]) =
      unify0(a.dive(lvl), b.dive(lvl))(lvl + 1)
    (forceMetas0(a), forceMetas0(b)) match
      case (VVar0(x), VVar0(y)) if x == y => ()
      case (VLet0(_, ty1, v1, b1), VLet0(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); unify0(v1, v2); goClos(b1, b2)
      case (VSplice(v1), VSplice(v2))         => unify1(v1, v2)
      case (VLam0(_, _, b1), VLam0(_, _, b2)) => goClos(b1, b2)
      case (VApp0(f1, a1), VApp0(f2, a2))     => unify0(f1, f2); unify0(a1, a2)
      case _ =>
        throw UnifyError(
          s"cannot unify ${quote0(a, UnfoldNone)} ~ ${quote0(b, UnfoldNone)}"
        )

  private def unify1(top1: Val1, sp1: Spine, top2: Val1, sp2: Spine)(implicit
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (SId, SId) => ()
      case (SApp(sp1, a1, _), SApp(sp2, a2, _)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case _ =>
        throw UnifyError(
          s"spine mismatch ${quote1(top1, UnfoldNone)} ~ ${quote1(top2, UnfoldNone)}"
        )

  def unify1(a: Val1, b: Val1)(implicit lvl: Lvl): Unit =
    inline def goClos(a: Clos[Tm1], b: Clos[Tm1]) =
      val v = VVar1(lvl)
      unify1(a(v), b(v))(lvl + 1)
    (forceMetas1(a), forceMetas1(b)) match
      case (top1 @ VUnfold(h1, sp1, v1), top2 @ VUnfold(h2, sp2, v2)) =>
        try
          if h1 != h2 then throw UnifyError("head mismatch")
          unify1(a, sp1, b, sp2)
        catch case _: UnifyError => unify1(v1(), v2())
      case (VUnfold(_, _, v1), v2) => unify1(v1(), v2)
      case (v1, VUnfold(_, _, v2)) => unify1(v1, v2())

      case (VRigid(x, sp1), VRigid(y, sp2)) if x == y => unify1(a, sp1, b, sp2)

      case (VLift(cv1, ty1), VLift(cv2, ty2)) =>
        unify1(cv1, cv2); unify1(ty1, ty2)
      case (VQuote(v1), VQuote(v2)) => unify0(v1, v2)
      case (VPi(_, i1, ty1, b1), VPi(_, i2, ty2, b2)) if i1 == i2 =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (VFun(t1, cv1, r1), VFun(t2, cv2, r2)) =>
        unify1(t1, t2); unify1(cv1, cv2); unify1(r1, r2)
      case (VCV1, VCV1)         => ()
      case (VComp, VComp)       => ()
      case (VVal, VVal)         => ()
      case (VU1, VU1)           => ()
      case (VU0(cv1), VU0(cv2)) => unify1(cv1, cv2)

      case (VLam1(_, _, _, b1), VLam1(_, _, _, b2)) => goClos(b1, b2)
      case (VLam1(_, i, _, b), f) =>
        val v = VVar1(lvl)
        unify1(b(v), vapp1(f, v, i))(lvl + 1)
      case (f, VLam1(_, i, _, b)) =>
        val v = VVar1(lvl)
        unify1(vapp1(f, v, i), b(v))(lvl + 1)

      case (top1 @ VFlex(id1, sp1), top2 @ VFlex(id2, sp2)) if id1 == id2 =>
        unify1(top1, sp1, top2, sp2)
      case (VFlex(id, sp), v) => solve(id, sp, v)
      case (v, VFlex(id, sp)) => solve(id, sp, v)

      case _ =>
        throw UnifyError(
          s"cannot unify ${quote1(a, UnfoldNone)} ~ ${quote1(b, UnfoldNone)}"
        )
