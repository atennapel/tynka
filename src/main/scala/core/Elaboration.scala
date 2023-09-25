package core

import common.Common.*
import common.Debug.*
import surface.Syntax as S
import Syntax.*
import Value.*
import Evaluation.*
import Unification.{UnifyError, unify1 as unify1_}
import Metas.*
import Globals.*
import Ctx.*

import scala.annotation.tailrec
import scala.collection.mutable
import surface.Syntax.Def

object Elaboration:
  private enum Infer:
    case Infer0(tm: Tm0, ty: VTy, cv: VCV)
    case Infer1(tm: Tm1, ty: VTy)
  import Infer.*

  // errors
  final case class ElaborateError(pos: PosInfo, msg: String)
      extends Exception(msg)

  private def error(msg: String)(implicit ctx: Ctx): Nothing =
    throw ElaborateError(ctx.pos, msg)

  // unification
  private def unify1(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
    debug(s"unify1 ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
    try unify1_(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        error(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  // metas
  private def closeType(ls: Locals, xs: List[Bind], ty: Ty): Ty = (ls, xs) match
    case (LEmpty, Nil) => ty
    case (LDef(ls, a, v), DoBind(x) :: xs) =>
      closeType(ls, xs, Let1(x, a, v, ty))
    case (LBind0(ls, a, cv), x :: xs) =>
      closeType(ls, xs, MetaPi(false, a, ty))
    case (LBind1(ls, a), x :: xs) => closeType(ls, xs, MetaPi(true, a, ty))
    case _                        => impossible()

  private def freshMeta(ty: VTy)(implicit ctx: Ctx): Tm1 =
    val qa = closeType(ctx.locals, ctx.binds, ctx.quote1(ty, UnfoldNone))
    val vqa = eval1(qa)(EEmpty)
    val m = newMeta(vqa)
    debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
    AppPruning(m, ctx.pruning)

  private inline def freshCV()(implicit ctx: Ctx): CV = freshMeta(VCV1)

  // meta insertion
  private enum InsertMode:
    case All
    case Until(name: Name)
  import InsertMode.*

  private def insertPi(inp: (Tm1, VTy), mode: InsertMode = All)(implicit
      ctx: Ctx
  ): (Tm1, VTy) =
    @tailrec
    def go(tm: Tm1, ty: VTy): (Tm1, VTy) =
      forceAll1(ty) match
        case VPi(y, Impl, a, b) =>
          mode match
            case Until(x) if DoBind(x) == y => (tm, ty)
            case _ =>
              val m = freshMeta(a)
              go(App1(tm, m, Impl), b(ctx.eval1(m)))
        case _ =>
          mode match
            case Until(x) => error(s"no implicit pi found with parameter $x")
            case _        => (tm, ty)
    go(inp._1, inp._2)

  private def insertPi(inp: Infer)(implicit ctx: Ctx): Infer = inp match
    case Infer0(t, a, cv) => inp
    case Infer1(t, a) =>
      val (t1, a1) = insertPi((t, a))
      Infer1(t1, a1)

  private def insert(inp: (Tm1, VTy))(implicit ctx: Ctx): (Tm1, VTy) =
    inp._1 match
      case Lam1(_, Impl, _, _) => inp
      case _                   => insertPi(inp)

  private def insert(inp: Infer)(implicit ctx: Ctx): Infer = inp match
    case Infer0(t, a, cv) => inp
    case Infer1(t, a) =>
      val (t1, a1) = insert((t, a))
      Infer1(t1, a1)

  // coercion lifting helpers
  private def liftFun(a: VTy, b: VTy, bcv: VCV)(implicit ctx: Ctx): VTy =
    implicit val l = ctx.lvl + 1
    val qbcv = quote1(bcv, UnfoldNone)
    val qb = quote1(b, UnfoldNone)
    VPi(DontBind, Expl, VLift(VVal, a), Clos(ctx.env, Lift(qbcv, qb)))

  private def quoteFun(a: VTy, t: Tm1)(implicit ctx: Ctx): Tm1 =
    Lam1(
      DoBind(Name("a")),
      Expl,
      Lift(Val, ctx.quote1(a)),
      Quote(App0(Wk10(splice(t)), Splice(Var1(ix0))))
    )

  private def spliceFun(a: VTy, t: Tm1)(implicit ctx: Ctx): Tm1 =
    Quote(
      Lam0(
        DoBind(Name("a")),
        ctx.quote1(a),
        Splice(App1(Wk01(t), Quote(Var0(ix0)), Expl))
      )
    )

  // coercion
  private def coe(t: Tm1, a1: VTy, a2: VTy)(implicit ctx: Ctx): Tm1 =
    def go(t: Tm1, a1: VTy, a2: VTy)(implicit ctx: Ctx): Option[Tm1] =
      (forceAll1(a1), forceAll1(a2)) match
        case (VFlex(x, sp), a2) => unify1(a1, a2); None
        case (a1, VFlex(x, sp)) => unify1(a1, a2); None

        case (VU0(cv), VU1) => Some(Lift(ctx.quote1(cv), t))

        case (VPi(x, i, a1, b1), VPi(x2, i2, a2, b2)) =>
          if i != i2 then error(s"icit mismatch in coercion")(ctx)
          implicit val ctx2: Ctx = ctx.bind1(x, ctx.quote1(a2), a2)
          go(Var1(ix0), a2, a1) match
            case None =>
              go(
                App1(Wk11(t), Var1(ix0), i),
                b1(ctx2.eval1(Var1(ix0))),
                b2(VVar1(ctx.lvl))
              ).map(b => Lam1(x, i, ctx.quote1(a2), b))
            case Some(coev0) =>
              Some(
                Lam1(
                  x,
                  i,
                  ctx.quote1(a2),
                  coe(
                    App1(Wk11(t), coev0, i),
                    b1(ctx2.eval1(coev0)),
                    b2(VVar1(ctx.lvl))
                  )
                )
              )

        case (VLift(_, VFun(a, cv, b)), a2) =>
          Some(coe(quoteFun(a, t), liftFun(a, b, cv), a2))
        case (a, VLift(_, VFun(t1, cv, t2))) =>
          Some(spliceFun(t1, coe(t, a, liftFun(t1, t2, cv))))

        case (pi @ VPi(x, Expl, a, b), VLift(cv, a2)) =>
          unify1(cv, VComp)
          val a1 = ctx.eval1(freshMeta(VU0(VVal)))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2_ = ctx.eval1(freshMeta(VU0(va2cv)))
          val fun = VFun(a1, va2cv, a2_)
          unify1(a2, fun)
          go(t, pi, VLift(VComp, fun))
        case (VLift(cv, a), pi @ VPi(x, Expl, t1, t2)) =>
          unify1(cv, VComp)
          val a1 = ctx.eval1(freshMeta(VU0(VVal)))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2 = ctx.eval1(freshMeta(VU0(va2cv)))
          val fun = VFun(a1, va2cv, a2)
          unify1(a, fun)
          go(t, VLift(VComp, fun), pi)

        case (a1, a2) => unify1(a1, a2); None

    go(t, a1, a2).getOrElse(t)

  // helpers
  private def tyAnnot(ma: Option[S.Tm], ty: VTy)(implicit ctx: Ctx): Ty =
    ma.fold(freshMeta(ty))(a => check1(a, ty))

  private def ensureFun(a: VTy, acv: VCV)(implicit ctx: Ctx): (VTy, VCV, VTy) =
    forceAll1(a) match
      case VFun(a, bcv, b) => (a, bcv, b)
      case _ =>
        unify1(acv, VComp)
        val a2 = ctx.eval1(freshMeta(VU0(VVal)))
        val bcv2 = freshCV()
        val vbcv2 = ctx.eval1(bcv2)
        val b2 = ctx.eval1(freshMeta(VU0(vbcv2)))
        unify1(a, VFun(a2, vbcv2, b2))
        (a2, vbcv2, b2)

  private def apply1(a: VTy, i: Icit, t: Tm1, u: S.Tm)(implicit
      ctx: Ctx
  ): Infer = forceAll1(a) match
    case VPi(x, i2, a, b) =>
      if i != i2 then error(s"icit mismatch in apply1")
      val u2 = check1(u, a)
      Infer1(App1(t, u2, i), b(ctx.eval1(u2)))
    case VLift(_, VFun(a, bcv, b)) =>
      if i != Expl then error(s"icit mismatch in apply1")
      val u2 = check0(u, a, VVal)
      Infer0(App0(splice(t), u2), b, bcv)
    case _ =>
      val a2 = freshMeta(VU1)
      val va2 = ctx.eval1(a2)
      val x = DoBind(Name("x"))
      val b2 = Clos(ctx.env, freshMeta(VU1)(ctx.bind1(x, a2, va2)))
      val t2 = coe(t, a, VPi(x, i, va2, b2))
      val u2 = check1(u, ctx.eval1(a2))
      Infer1(App1(t2, u2, i), b2(ctx.eval1(u2)))

  private def coeQuote(t: Tm1, a1: VTy, a2: VTy, cv: VCV)(implicit
      ctx: Ctx
  ): Tm0 =
    splice(coe(t, a1, VLift(cv, a2)))

  // checking
  private def check0(tm: S.Tm, ty: VTy, cv: VCV)(implicit ctx: Ctx): Tm0 =
    debug(s"check0 $tm : ${ctx.pretty(ty)} : ${ctx.pretty(cv)}")
    tm match
      case S.Pos(pos, tm) => check0(tm, ty, cv)(ctx.enter(pos))

      case S.Lam(x, i, ma, b) =>
        if i != S.ArgIcit(Expl) then error(s"implicit lambda in Ty")
        val (t1, fcv, t2) = ensureFun(ty, cv)
        ma.foreach { sty => unify1(ctx.eval1(check1(sty, VU0(VVal))), t1) }
        val qt1 = ctx.quote1(t1)
        Lam0(x, qt1, check0(b, t2, fcv)(ctx.bind0(x, qt1, t1, Val, VVal)))

      case S.Let(x, rec, false, ma, v, b) =>
        val (ety, cv2, vcv2) =
          if rec then (tyAnnot(ma, VU0(VComp)), Comp, VComp)
          else
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(ma, VU0(vcv2))
            (ety, cv2, vcv2)
        val vty = ctx.eval1(ety)
        val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
        val ev = check0(v, vty, vcv2)(if rec then nctx else ctx)
        val eb = check0(b, ty, cv)(nctx)
        if rec then LetRec(x, ety, ev, eb) else Let0(x, ety, ev, eb)

      case S.Hole(_) => splice(freshMeta(VLift(cv, ty)))

      case S.Splice(t) => splice(check1(t, VLift(cv, ty)))

      case tm =>
        infer(tm) match
          case Infer0(etm, vty, vcv) =>
            unify1(vcv, cv)
            unify1(vty, ty)
            etm
          case Infer1(etm, vty) => coeQuote(etm, vty, ty, cv)

  private def icitMatch(i: S.ArgInfo, x: Bind, i2: Icit): Boolean = i match
    case S.ArgNamed(y) =>
      x match
        case DontBind  => false
        case DoBind(x) => x == y
    case S.ArgIcit(i) => i == i2

  private def check1(tm: S.Tm, ty: VTy)(implicit ctx: Ctx): Tm1 =
    debug(s"check1 $tm : ${ctx.pretty(ty)}")
    (tm, forceAll1(ty)) match
      case (S.Pos(pos, tm), _) => check1(tm, ty)(ctx.enter(pos))

      case (S.Lam(x, i, ma, b), VPi(x2, i2, t1, t2)) if icitMatch(i, x2, i2) =>
        ma.foreach { sty => unify1(ctx.eval1(check1(sty, VU1)), t1) }
        val qt1 = ctx.quote1(t1)
        Lam1(x, i2, qt1, check1(b, t2(VVar1(ctx.lvl)))(ctx.bind1(x, qt1, t1)))
      case (tm, VPi(x, Impl, t1, t2)) =>
        val qt1 = ctx.quote1(t1)
        Lam1(x, Impl, qt1, check1(tm, t2(VVar1(ctx.lvl)))(ctx.insert(x, qt1)))

      case (S.Pi(DontBind, Expl, t1, t2), VU0(cv)) =>
        unify1(cv, VComp)
        val et1 = check1(t1, VU0(VVal))
        val fcv = freshCV()
        val vfcv = ctx.eval1(fcv)
        val et2 = check1(t2, VU0(vfcv))
        Fun(et1, fcv, et2)
      case (S.Pi(x, i, t1, t2), VU1) =>
        val et1 = check1(t1, VU1)
        val et2 = check1(t2, VU1)(ctx.bind1(x, et1, ctx.eval1(et1)))
        Pi(x, i, et1, et2)

      case (S.Lift(tm), VU1) =>
        val cv = freshCV()
        Lift(cv, check1(tm, VU0(ctx.eval1(cv))))

      case (S.Let(x, rec, true, mlty, v, b), _) =>
        if rec then error("let rec is not allowed for meta definitions")
        val lty = tyAnnot(mlty, VU1)
        val vlty = ctx.eval1(lty)
        val ev = check1(v, vlty)
        val eb = check1(b, ty)(ctx.define(x, lty, vlty, ev, ctx.eval1(ev)))
        Let1(x, lty, ev, eb)

      case (S.Quote(tm), VLift(cv, ty)) => quote(check0(tm, ty, cv))
      case (tm, VLift(cv, ty))          => quote(check0(tm, ty, cv))

      case (S.Hole(_), _) => freshMeta(ty)

      case (tm, _) =>
        val (etm, vty) = insert(infer1(tm))
        coe(etm, vty, ty)

  // inference
  private def infer0(tm: S.Tm)(implicit ctx: Ctx): (Tm0, VTy, VCV) =
    debug(s"infer0 $tm")
    tm match
      case S.Pos(pos, tm) => infer0(tm)(ctx.enter(pos))

      case S.Lam(x, i, mty, b) =>
        i match
          case S.ArgNamed(_)   => error(s"implicit lambda in Ty")
          case S.ArgIcit(Impl) => error(s"implicit lambda in Ty")
          case S.ArgIcit(Expl) =>
            val ety = tyAnnot(mty, VU0(VVal))
            val cv = freshCV()
            val vcv = ctx.eval1(cv)
            val rt = freshMeta(VU0(vcv))
            val vrt = ctx.eval1(rt)
            val vty = ctx.eval1(ety)
            val eb = check0(b, vrt, vcv)(ctx.bind0(x, ety, vty, Val, VVal))
            (Lam0(x, ety, eb), VFun(vty, vcv, vrt), VComp)

      case tm =>
        insert(infer(tm)) match
          case Infer0(etm, ty, cv) => (etm, ty, cv)
          case Infer1(etm, ty) =>
            forceAll1(ty) match
              case VLift(cv, vty) => (splice(etm), vty, cv)
              case _ =>
                val cv = freshCV()
                val vcv = ctx.eval1(cv)
                val vty = ctx.eval1(freshMeta(VU0(vcv)))
                val etm2 = splice(coe(etm, ty, VLift(vcv, vty)))
                (etm2, vty, vcv)

  private def infer1(tm: S.Tm)(implicit ctx: Ctx): (Tm1, VTy) =
    debug(s"infer1 $tm")
    tm match
      case S.Pos(pos, tm) => infer1(tm)(ctx.enter(pos))

      case S.Lam(x, i, mty, b) =>
        i match
          case S.ArgNamed(_) => error(s"cannot infer named lambda")
          case S.ArgIcit(i) =>
            val ety = tyAnnot(mty, VU1)
            val vty = ctx.eval1(ety)
            val ctx2 = ctx.bind1(x, ety, vty)
            val (eb, vrt) = insert(infer1(b)(ctx2))(ctx2)
            val ert = ctx2.quote1(vrt)
            (Lam1(x, i, ety, eb), VPi(x, i, vty, Clos(ctx.env, ert)))

      case tm =>
        infer(tm) match
          case Infer0(tm, ty, cv) => (quote(tm), VLift(cv, ty))
          case Infer1(tm, ty)     => (tm, ty)

  private def infer(tm: S.Tm)(implicit ctx: Ctx): Infer =
    debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))

      case S.Var(Name("Bool")) => Infer1(Prim1(Name("Bool")), VU0(VVal))
      case S.Var(Name("True")) =>
        Infer0(Prim0(Name("True")), VPrim1(Name("Bool")), VVal)
      case S.Var(Name("False")) =>
        Infer0(Prim0(Name("False")), VPrim1(Name("Bool")), VVal)
      case S.Var(Name("caseBool")) =>
        // {cv} {A : Ty cv} -> Bool -> A -> A -> A
        val cv = Name("cv")
        val a = Name("A")
        val va = S.Var(a)
        val sty = S.Pi(
          DoBind(cv),
          Impl,
          S.Hole(None),
          S.Pi(
            DoBind(a),
            Impl,
            S.U0(S.Var(cv)),
            S.Pi(
              DontBind,
              Expl,
              S.Var(Name("Bool")),
              S.Pi(
                DontBind,
                Expl,
                va,
                S.Pi(DontBind, Expl, va, va)
              )
            )
          )
        )
        val ety = check1(sty, VU1)
        Infer1(Prim1(Name("caseBool")), ctx.eval1(ety))

      case S.Var(Name("Nat")) => Infer1(Prim1(Name("Nat")), VU0(VVal))
      case S.Var(Name("Z")) =>
        Infer0(Prim0(Name("Z")), VPrim1(Name("Nat")), VVal)
      case S.Var(Name("S")) =>
        // ^Nat -> ^Nat
        // \n. `(S $n)
        val nat = Name("Nat")
        val lnat = VLift(VVal, VPrim1(nat))
        val qnat = Lift(Val, Prim1(nat))
        Infer1(
          Lam1(
            DoBind(Name("n")),
            Expl,
            qnat,
            Quote(App0(Prim0(Name("S")), Splice(Var1(ix0))))
          ),
          VPi(DontBind, Expl, lnat, Clos(EEmpty, qnat))
        )
      case S.Var(Name("caseNat")) =>
        // {cv} {A : Ty cv} -> Nat -> A -> (Nat -> A) -> A
        val cv = Name("cv")
        val a = Name("A")
        val nat = Name("Nat")
        val va = S.Var(a)
        val sty = S.Pi(
          DoBind(cv),
          Impl,
          S.Hole(None),
          S.Pi(
            DoBind(a),
            Impl,
            S.U0(S.Var(cv)),
            S.Pi(
              DontBind,
              Expl,
              S.Var(nat),
              S.Pi(
                DontBind,
                Expl,
                va,
                S.Pi(
                  DontBind,
                  Expl,
                  S.Pi(
                    DontBind,
                    Expl,
                    S.Var(nat),
                    va
                  ),
                  va
                )
              )
            )
          )
        )
        val ety = check1(sty, VU1)
        Infer1(Prim1(Name("caseNat")), ctx.eval1(ety))

      case S.Var(x) =>
        ctx.lookup(x) match
          case Some(Name0(x, ty, cv)) => Infer0(Var0(x.toIx(ctx.lvl)), ty, cv)
          case Some(Name1(x, ty))     => Infer1(Var1(x.toIx(ctx.lvl)), ty)
          case None =>
            getGlobal(x) match
              case None => error(s"undefined variable $x")
              case Some(GlobalEntry0(_, _, _, _, _, ty, cv)) =>
                Infer0(Global0(x), ty, cv)
              case Some(GlobalEntry1(_, _, _, _, ty)) =>
                Infer1(Global1(x), ty)

      case S.Let(x, rec, false, mty, v, b) =>
        val (ety, cv2, vcv2) =
          if rec then (tyAnnot(mty, VU0(VComp)), Comp, VComp)
          else
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(mty, VU0(vcv2))
            (ety, cv2, vcv2)
        val vty = ctx.eval1(ety)
        val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
        val ev = check0(v, vty, vcv2)(if rec then nctx else ctx)
        val (eb, rty, rcv) = infer0(b)(nctx)
        Infer0(
          if rec then LetRec(x, ety, ev, eb) else Let0(x, ety, ev, eb),
          rty,
          rcv
        )
      case S.Let(x, rec, true, mty, v, b) =>
        if rec then error("let rec is not allowed in meta definitions")
        val lty = tyAnnot(mty, VU1)
        val vlty = ctx.eval1(lty)
        val ev = check1(v, vlty)
        val (eb, rty) =
          infer1(b)(ctx.define(x, lty, vlty, ev, ctx.eval1(ev)))
        Infer1(Let1(x, lty, ev, eb), rty)

      case S.Pi(DontBind, Expl, a, b) =>
        val (ea, vta) = insert(infer1(a))
        forceAll1(vta) match
          case VU0(cv) =>
            unify1(cv, VVal)
            val bcv = freshCV()
            val vbcv = ctx.eval1(bcv)
            val eb = check1(b, VU0(vbcv))
            Infer1(Fun(ea, bcv, eb), VU0(VComp))
          case VU1 =>
            val eb = check1(b, VU1)(ctx.bind1(DontBind, ea, ctx.eval1(ea)))
            Infer1(Pi(DontBind, Expl, ea, eb), VU1)
          case _ => error("expected type for Pi parameter")
      case S.Pi(x, i, a, b) =>
        val ea = check1(a, VU1)
        val eb = check1(b, VU1)(ctx.bind1(x, ea, ctx.eval1(ea)))
        Infer1(Pi(x, i, ea, eb), VU1)

      case S.Lam(x, i, mty, b) =>
        i match
          case S.ArgNamed(_)   => error("cannot infer")
          case S.ArgIcit(Expl) => error("cannot infer")
          case S.ArgIcit(Impl) =>
            val ety = tyAnnot(mty, VU1)
            val vty = ctx.eval1(ety)
            val ctx2 = ctx.bind1(x, ety, vty)
            val (eb, vrt) = insert(infer1(b)(ctx2))(ctx2)
            val qrt = ctx2.quote1(vrt)
            Infer1(
              Lam1(x, Impl, ety, eb),
              VPi(x, Impl, vty, Clos(ctx.env, qrt))
            )

      case S.App(f, a, i) =>
        i match
          case S.ArgNamed(x) =>
            val (ef, fty) = insertPi(infer1(f), Until(x))
            apply1(fty, Impl, ef, a)
          case S.ArgIcit(Impl) =>
            val (ef, fty) = infer1(f)
            apply1(fty, Impl, ef, a)
          case S.ArgIcit(Expl) =>
            insertPi(infer(f)) match
              case Infer0(ef, fty, fcv) =>
                val (t1, rcv, t2) = ensureFun(fty, fcv)
                val ea = check0(a, t1, VVal)
                Infer0(App0(ef, ea), t2, rcv)
              case Infer1(ef, fty) => apply1(fty, Expl, ef, a)

      case S.Lift(ty) =>
        val cv = freshCV()
        val vcv = ctx.eval1(cv)
        Infer1(Lift(cv, check1(ty, VU0(vcv))), VU1)
      case S.Quote(tm) =>
        val (etm, vty, vcv) = infer0(tm)
        Infer1(quote(etm), VLift(vcv, vty))
      case S.Splice(tm) =>
        val (etm, vty) = insert(infer1(tm))
        forceAll1(vty) match
          case VLift(cv, a) => Infer0(splice(etm), a, cv)
          case vty =>
            val cv = freshCV()
            val vcv = ctx.eval1(cv)
            val vty2 = ctx.eval1(freshMeta(VU0(vcv)))
            val etm2 = splice(coe(etm, vty, VLift(vcv, vty2)))
            Infer0(etm2, vty2, vcv)

      case S.U0(cv) => Infer1(U0(check1(cv, VCV1)), VU1)
      case S.U1     => Infer1(U1, VU1)
      case S.CV     => Infer1(CV1, VU1)
      case S.Comp   => Infer1(Comp, VCV1)
      case S.Val    => Infer1(Val, VCV1)

      case S.Hole(_) => error("cannot infer hole")

  // elaboration
  def elaborate(d: S.Def): Unit = d match
    case S.DDef(pos, x, rec, m, mty, v) =>
      implicit val ctx: Ctx = Ctx.empty(pos)
      if getGlobal(x).isDefined then error(s"duplicated definition $x")
      if m then
        if rec then error("def rec not allowed in meta definitions")
        val (ev, ty, vv, vty) = mty match
          case None =>
            val (ev, vty) = infer1(v)
            (ev, ctx.quote1(vty), ctx.eval1(ev), vty)
          case Some(sty) =>
            val ety = check1(sty, VU1)
            val vty = ctx.eval1(ety)
            val ev = check1(v, vty)
            (ev, ety, ctx.eval1(ev), vty)
        setGlobal(GlobalEntry1(x, ev, ty, vv, vty))
      else
        val (ev, ty, cv, vty, vcv) = mty match
          case None if !rec =>
            val (ev, vty, vcv) = infer0(v)
            (ev, ctx.quote1(vty), ctx.quote1(vcv), vty, vcv)
          case _ =>
            val cv = if rec then Comp else freshCV()
            val vcv = ctx.eval1(cv)
            val ety = mty match
              case None      => freshMeta(VU0(vcv))
              case Some(sty) => check1(sty, VU0(vcv))
            val vty = ctx.eval1(ety)
            val ev = check0(v, vty, vcv)(
              if rec then ctx.bind0(DoBind(x), ety, vty, cv, vcv) else ctx
            )
            (
              if rec then LetRec(x, ety, ev, Var0(ix0)) else ev,
              ety,
              cv,
              vty,
              vcv
            )
        setGlobal(GlobalEntry0(x, ev, ty, cv, ctx.eval0(ev), vty, vcv))

  def elaborate(d: S.Defs): Unit = d.toList.foreach(elaborate)

  def elaborate(tm: S.Tm): (Either[Tm0, Tm1], Ty) =
    implicit val ctx: Ctx = Ctx.empty((0, 0))
    infer(tm) match
      case Infer0(etm, ty, _) => (Left(etm), ctx.quote1(ty))
      case Infer1(etm, ty)    => (Right(etm), ctx.quote1(ty))

  def elaborate1(tm: S.Tm): (Tm1, Ty) =
    implicit val ctx: Ctx = Ctx.empty((0, 0))
    val (etm, ty) = infer1(tm)
    (etm, ctx.quote1(ty, UnfoldMetas))

  def elaborate0(tm: S.Tm): (Tm0, Ty) =
    implicit val ctx: Ctx = Ctx.empty((0, 0))
    val (etm, ty, _) = infer0(tm)
    (etm, ctx.quote1(ty, UnfoldMetas))
