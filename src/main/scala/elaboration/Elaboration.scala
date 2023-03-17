package elaboration

import common.Common.*
import common.Debug.*
import surface.Syntax as S
import core.Syntax.*
import core.Value.*
import core.Evaluation.*
import core.Unification.{UnifyError, unify as unify0}
import core.Metas.*
import core.Globals.*
import Ctx.*

import scala.annotation.tailrec
import scala.collection.mutable

object Elaboration:
  // errors
  final case class ElaborateError(pos: PosInfo, uri: String, msg: String)
      extends Exception(msg)

  private def error(msg: String)(implicit ctx: Ctx): Nothing =
    throw ElaborateError(ctx.pos, null, msg)

  // unification
  private def unify(a: VStage, b: VStage)(implicit ctx: Ctx): Unit =
    debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
    try unify0(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        error(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  private def unify(a: Val, b: Val)(implicit ctx: Ctx): Unit =
    debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
    try unify0(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        error(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  // holes
  private final case class HoleEntry(
      ctx: Ctx,
      tm: Tm,
      ty: VTy,
      stage: VStage
  )
  private val holes: mutable.ArrayBuffer[(Name, HoleEntry)] =
    mutable.ArrayBuffer.empty

  private def addHole(x: Name, h: HoleEntry)(implicit ctx: Ctx): Unit =
    if holes.find((y, _) => x == y).isDefined then error(s"duplicate hole _$x")
    holes += x -> h

  // import names
  private type Imported = mutable.Map[Name, (String, Name)]
  private val imported: Imported = mutable.Map.empty

  // metas
  private def newMeta(ty: VTy, s: VStage)(implicit ctx: Ctx): Tm =
    val closed = ctx.closeVTy(ty)
    val m = freshMeta(closed, s)
    debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
    AppPruning(Meta(m), ctx.pruning)

  private def newVF()(implicit ctx: Ctx): Tm = newMeta(VVF, SMeta)

  private enum InsertMode:
    case All
    case Until(name: Name)
  import InsertMode.*

  private def insertPi(inp: (Tm, VTy, VStage), mode: InsertMode = All)(implicit
      ctx: Ctx
  ): (Tm, VTy, VStage) =
    @tailrec
    def go(tm: Tm, ty: VTy, st: VStage): (Tm, VTy, VStage) =
      force(ty) match
        case VPi(y, Impl, a, b) =>
          mode match
            case Until(x) if DoBind(x) == y => (tm, ty, st)
            case _ =>
              val m = newMeta(a, st)
              val mv = ctx.eval(m)
              go(App(tm, m, Impl), b(mv), st)
        case _ =>
          mode match
            case Until(x) => error(s"no implicit pi found with parameter $x")
            case _        => (tm, ty, st)
    go(inp._1, inp._2, inp._3)

  private def insert(inp: (Tm, VTy, VStage))(implicit
      ctx: Ctx
  ): (Tm, VTy, VStage) =
    inp._1 match
      case Lam(_, Impl, _, _) => inp
      case _                  => insertPi(inp)

  private def insert(s: VStage, inp: (Tm, VTy))(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    val res = insert((inp._1, inp._2, s))
    (res._1, res._2)

  // coercion
  private def tryAdjustStage(t: Tm, a: VTy, s1: VStage, s2: VStage)(implicit
      ctx: Ctx
  ): Option[(Tm, VTy)] =
    debug(
      s"tryAdjustStage $t : ${ctx.pretty(a)} : ${ctx.pretty(s1)} to ${ctx.pretty(s2)}"
    )
    (s1, s2) match
      case (SMeta, SMeta)       => None
      case (STy(vf1), STy(vf2)) => unify(vf1, vf2); None
      case (STy(vf), SMeta)     => Some((t.quote, VLift(vf, a)))
      case (SMeta, STy(vf)) =>
        debug(s"$t : ${ctx.pretty(a)} : ${ctx.pretty(s1)} to ${ctx.pretty(s2)}")
        val m = ctx.eval(newMeta(VUTy(vf), SMeta))
        unify(a, VLift(vf, m))
        Some((t.splice, m))

  private def adjustStage(t: Tm, a: VTy, s1: VStage, s2: VStage)(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    debug(
      s"adjustStage $t : ${ctx.pretty(a)} : ${ctx.pretty(s1)} to ${ctx.pretty(s2)}"
    )
    tryAdjustStage(t, a, s1, s2).fold((t, a))(x => x)

  private def coe(t: Tm, a: VTy, st1: VStage, b: VTy, st2: VStage)(implicit
      ctx: Ctx
  ): Tm =
    debug(
      s"coeTop ${ctx.pretty(t)} : ${ctx.pretty(a)} : ${ctx.pretty(st1)} to ${ctx
          .pretty(b)} : ${ctx.pretty(st2)}"
    )
    def pick(x: Bind, y: Bind)(implicit ctx: Ctx): Bind = ctx.fresh((x, y) match
      case (DontBind, DontBind) => DoBind(Name("x"))
      case (DontBind, x)        => x
      case (x, DontBind)        => x
      case (_, x)               => x
    )
    def justAdjust(t: Tm, a: VTy, st1: VStage, b: VTy, st2: VStage)(implicit
        ctx: Ctx
    ): Option[Tm] =
      debug(
        s"justAdjust $t : ${ctx.pretty(a)} : ${ctx.pretty(st1)} to ${ctx
            .pretty(b)} : ${ctx.pretty(st2)}"
      )
      tryAdjustStage(t, a, st1, st2) match
        case None         => unify(st1, st2); unify(a, b); None
        case Some((t, a)) => unify(a, b); Some(t)
    def go(
        t: Tm,
        a: VTy,
        st1: VStage,
        b: VTy,
        st2: VStage
    )(implicit ctx: Ctx): Option[Tm] =
      debug(
        s"coe ${ctx.pretty(t)} : ${ctx.pretty(a)} : ${ctx.pretty(st1)} to ${ctx
            .pretty(b)} : ${ctx.pretty(st2)}"
      )
      (force(a), force(b)) match
        case (VPi(x, i, p1, r1), VPi(x2, i2, p2, r2)) =>
          if i != i2 then
            error(
              s"plicity mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          val ctx2 = ctx.bind(x, p2, SMeta)
          go(Var(ix0), p2, SMeta, p1, SMeta)(ctx2) match
            case None =>
              val v = VVar(ctx.lvl)
              val body =
                go(App(Wk(t), Var(ix0), i), r1(v), SMeta, r2(v), SMeta)(ctx2)
              body.map(Lam(pick(x, x2), i, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i),
                r1(ctx2.eval(coev0)),
                SMeta,
                r2(VVar(ctx.lvl)),
                SMeta
              )(ctx2) match
                case None =>
                  Some(Lam(pick(x, x2), i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(pick(x, x2), i, ctx.quote(b), body))

        case (VTFun(p1, vf, r1), VTFun(p2, vf2, r2)) =>
          unify(vf, vf2)
          val x = DoBind(Name("x"))
          val ctx2 = ctx.bind(x, p2, SVTy())
          go(Var(ix0), p2, SVTy(), p1, SVTy())(ctx2) match
            case None =>
              val body =
                go(App(Wk(t), Var(ix0), Expl), r1, STy(vf), r2, STy(vf))(ctx2)
              body.map(Lam(x, Expl, ctx.quote(b), _))
            case Some(coev0) =>
              go(App(Wk(t), coev0, Expl), r1, STy(vf), r2, STy(vf))(ctx2) match
                case None =>
                  Some(Lam(x, Expl, ctx.quote(b), App(Wk(t), coev0, Expl)))
                case Some(body) => Some(Lam(x, Expl, ctx.quote(b), body))

        case (VTFun(p1, vf, r1), VPi(x, i, p2, r2)) =>
          if i == Impl then
            error(s"coerce error ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          val ctx2 = ctx.bind(x, p2, SMeta)
          val y = DoBind(Name("x"))
          go(Var(ix0), p2, SMeta, p1, SVTy())(ctx2) match
            case None =>
              val body =
                go(
                  App(Wk(t), Var(ix0), i),
                  r1,
                  STy(vf),
                  r2(VVar(ctx.lvl)),
                  SMeta
                )(
                  ctx2
                )
              body.map(Lam(pick(y, x), i, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i),
                r1,
                STy(vf),
                r2(VVar(ctx.lvl)),
                SMeta
              )(ctx2) match
                case None =>
                  Some(Lam(pick(y, x), i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(pick(y, x), i, ctx.quote(b), body))
        case (VPi(x, i, p1, r1), VTFun(p2, vf, r2)) =>
          if i == Impl then
            error(s"coerce error ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          val ctx2 = ctx.bind(x, p2, SVTy())
          val y = DoBind(Name("x"))
          go(Var(ix0), p2, SVTy(), p1, SMeta)(ctx2) match
            case None =>
              val body =
                go(
                  App(Wk(t), Var(ix0), i),
                  r1(VVar(ctx.lvl)),
                  SMeta,
                  r2,
                  STy(vf)
                )(
                  ctx2
                )
              body.map(Lam(pick(y, x), i, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i),
                r1(ctx2.eval(coev0)),
                SMeta,
                r2,
                STy(vf)
              )(ctx2) match
                case None =>
                  Some(Lam(pick(y, x), i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(pick(y, x), i, ctx.quote(b), body))

        case (VU(STy(vf)), VU(SMeta)) => Some(Lift(ctx.quote(vf), t))
        case (VFlex(_, _), _)         => justAdjust(t, a, st1, b, st2)
        case (_, VFlex(_, _))         => justAdjust(t, a, st1, b, st2)
        case (VLift(vf1, a), VLift(vf2, b)) =>
          unify(vf1, vf2); unify(a, b); None
        case (VLift(vf, a), b) => Some(coe(t.splice, a, STy(vf), b, st2))
        case (a, VLift(vf, b)) => Some(coe(t, a, st1, b, STy(vf)).quote)
        case _                 => justAdjust(t, a, st1, b, st2)
    go(t, a, st1, b, st2).getOrElse(t)

  // checking
  private def icitMatch(i1: S.ArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case S.ArgNamed(x) =>
      (b, i2) match
        case (DoBind(y), Impl) => x == y
        case _                 => false
    case S.ArgIcit(i) => i == i2

  private def hasMetaType(x: Name)(implicit ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some((_, vty, SMeta)) =>
        force(vty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def checkType(ty: S.Ty, s: VStage)(implicit ctx: Ctx): Tm =
    check(ty, VU(s), SMeta)
  private def checkVTy(ty: S.Ty)(implicit ctx: Ctx): Tm =
    check(ty, VVTy(), SMeta)

  private def check(tm: S.Tm, ty: Option[S.Ty], stage: VStage)(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy) = ty match
    case Some(ty) =>
      val ety = checkType(ty, stage)
      val vty = ctx.eval(ety)
      val etm = check(tm, vty, stage)
      (etm, ety, vty)
    case None =>
      val (etm, vty) = infer(tm, stage)
      (etm, ctx.quote(vty), vty)

  private def check(tm: S.Tm, ty: VTy, stage: VStage)(implicit ctx: Ctx): Tm =
    if !tm.isPos then
      debug(s"check $tm : ${ctx.pretty(ty)} : ${ctx.pretty(stage)}")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty, stage)(ctx.enter(pos))

      case (S.Lam(x, i, ot, b), VPi(y, i2, a, rt)) if icitMatch(i, y, i2) =>
        ot.foreach(t0 => {
          val ety = checkType(t0, SMeta)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, ctx.inst(rt), SMeta)(ctx.bind(x, a, SMeta))
        Lam(x, i2, ctx.quote(ty), eb)
      case (S.Lam(x, S.ArgIcit(Expl), ot, b), VTFun(a, vf, rt)) =>
        ot.foreach(t0 => {
          val ety = checkVTy(t0)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, rt, STy(vf))(ctx.bind(x, a, SVTy()))
        Lam(x, Expl, ctx.quote(ty), eb)
      case (S.Var(x), VPi(_, Impl, _, _)) if hasMetaType(x) =>
        val Some((ix, varty, SMeta)) = ctx.lookup(x): @unchecked
        unify(varty, ty)
        Var(ix)
      case (tm, VPi(x, Impl, a, b)) =>
        val etm = check(tm, ctx.inst(b), SMeta)(ctx.bind(x, a, SMeta, true))
        Lam(x, Impl, ctx.quote(ty), etm)

      case (S.Lift(a), VU(SMeta)) =>
        val vf = ctx.eval(newVF())
        Lift(ctx.quote(vf), checkType(a, STy(vf)))

      case (S.Pi(x, i, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Pi(x, i, ea, eb)
      case (S.Pi(x, Expl, a, b), VUTy(vf)) =>
        unify(vf, VFun)
        val ea = checkType(a, SVTy())
        val vf2 = newVF()
        val eb = checkType(b, STy(ctx.eval(vf2)))
        TFun(ea, vf2, eb)

      case (S.Fix(g, x, b, arg), _) if !stage.isMeta =>
        val STy(vf) = stage: @unchecked
        val (earg, pty) = infer(arg, SVTy())
        val eb =
          check(b, ty, STy(vf))(
            ctx.bind(g, VTFun(pty, vf, ty), SFTy()).bind(x, pty, SVTy())
          )
        Fix(ctx.quote(pty), ctx.quote(ty), g, x, eb, earg)

      case (S.Quote(t), VLift(vf, a)) => check(t, a, STy(vf)).quote
      case (t, VLift(vf, a))          => check(t, a, STy(vf)).quote

      case (S.Let(x, m, t, v, b), _) if stage.isMeta == m =>
        val valstage = if m then SMeta else STy(newVF())
        val vvalstage = ctx.eval(valstage)
        val (ev, et, vt) = check(v, t, vvalstage)
        val qstage = ctx.quote(stage)
        val eb = check(b, ty, stage)(
          ctx.define(x, vt, et, vvalstage, valstage, ctx.eval(ev), ev)
        )
        Let(x, et, valstage, ctx.quote(ty), ev, eb)

      case (S.Hole(ox), _) =>
        val t = newMeta(ty, stage)
        ox.foreach(x => addHole(x, HoleEntry(ctx, t, ty, stage)))
        t

      case (t, VFlex(_, _)) =>
        val (etm, vt) = insert(stage, infer(t, stage))
        coe(etm, vt, stage, ty, stage)
      case _ =>
        val (etm, ty2, stage2) = insert(infer(tm))
        coe(etm, ty2, stage2, ty, stage)

  // inference
  private def inferType(ty: S.Ty)(implicit ctx: Ctx): (Tm, VStage) =
    val (t, a) = infer(ty, SMeta)
    force(a) match
      case VU(s) => (t, s)
      case ty    => error(s"expected type got ${ctx.pretty(ty)}")

  private def infer(tm: S.Tm, s: VStage)(implicit ctx: Ctx): (Tm, VTy) =
    if !tm.isPos then debug(s"infer $tm : ${ctx.pretty(s)}")
    tm match
      case S.Pos(pos, tm) => infer(tm, s)(ctx.enter(pos))

      case S.Lam(x, S.ArgIcit(i), ot, b) =>
        s match
          case SMeta =>
            val a = ot match
              case None     => newMeta(VU(SMeta), SMeta)
              case Some(ty) => checkType(ty, SMeta)
            val va = ctx.eval(a)
            val (eb, rt) = infer(b, SMeta)(ctx.bind(x, va, SMeta))
            (Lam(x, i, Irrelevant, eb), VPi(x, i, va, ctx.close(rt)))
          case STy(vfr) =>
            if i == Impl then error(s"implicit lambda cannot be in Ty: $tm")
            unify(vfr, VFun)
            val a = ot match
              case None     => newMeta(VVTy(), SMeta)
              case Some(ty) => checkVTy(ty)
            val va = ctx.eval(a)
            val vf = ctx.eval(newVF())
            val rty0 = ctx.eval(newMeta(VUTy(vf), SMeta))
            val ctx2 = ctx.bind(x, va, SVTy())
            val eb0 = check(b, rty0, STy(vf))(ctx2)
            val (eb, rty) = insert(STy(vf), (eb0, rty0))(ctx2)
            val fty = VTFun(va, vf, rty)
            (Lam(x, Expl, ctx.quote(fty), eb), fty)
      case S.Lam(x, S.ArgNamed(_), _, _) => error(s"cannot infer $tm")

      case S.Hole(ox) =>
        val ty = ctx.eval(newMeta(VU(s), SMeta))
        val t = newMeta(ty, s)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty, s))
        (t, ty)

      case S.Fix(g, x, b, arg) if !s.isMeta =>
        val STy(vf) = s: @unchecked
        val (earg, vty) = infer(arg, SVTy())
        val rty = newMeta(VUTy(vf), SMeta)
        val vrty = ctx.eval(rty)
        val ft = VTFun(vty, vf, vrty)
        val eb =
          check(b, vrty, STy(vf))(ctx.bind(g, ft, SFTy()).bind(x, vty, SVTy()))
        (Fix(ctx.quote(vty), rty, g, x, eb, earg), vrty)

      case _ =>
        val (t, a, si) = insert(infer(tm))
        debug(
          s"inferred $t : ${ctx.pretty(a)} : ${ctx.pretty(si)} to ${ctx.pretty(s)}"
        )
        adjustStage(t, a, si, s)

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, VStage) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))
      case S.Hole(ox)     => error(s"cannot infer hole $tm")
      case S.TInt         => (TInt, VVTy(), SMeta)
      case S.IntLit(n)    => (IntLit(n), VTInt, STy(VVal))
      case S.VF           => (VF, VUMeta(), SMeta)
      case S.VFVal        => (VFVal, VVF, SMeta)
      case S.VFFun        => (VFFun, VVF, SMeta)
      case S.U(SMeta)     => (U(SMeta), VUMeta(), SMeta)
      case S.U(STy(vf)) =>
        val evf = check(vf, VVF, SMeta)
        (U(STy(evf)), VU(SMeta), SMeta)
      case S.Var(x) =>
        if !x.isOperator && x.expose.contains(":") then
          val s = x.expose.split("\\:")
          val mod = s.head
          val y = Name(s.tail.mkString(":"))
          getGlobal(mod, y) match
            case Some(e) => (Global(mod, y), e.vty, e.vstage)
            case None    => error(s"undefined variable $x")
        else
          ctx.lookup(x) match
            case Some((ix, ty, u)) => (Var(ix), ty, u)
            case None =>
              getGlobal(ctx.module, x) match
                case Some(e) => (Global(ctx.module, x), e.vty, e.vstage)
                case None =>
                  imported.get(x) match
                    case Some((m, y)) =>
                      getGlobal(m, y) match
                        case Some(e) => (Global(m, y), e.vty, e.vstage)
                        case None    => error(s"undefined variable $x")
                    case None => error(s"undefined variable $x")

      case S.Let(x, m, t, v, b) =>
        val stage1 = if m then SMeta else STy(newVF())
        val vstage1 = ctx.eval(stage1)
        val stage2 = if m then SMeta else STy(newVF())
        val vstage2 = ctx.eval(stage2)
        val (ev, et, vt) = check(v, t, vstage1)
        val (eb, rt) =
          infer(b, vstage2)(
            ctx.define(x, vt, et, vstage1, stage1, ctx.eval(ev), ev)
          )
        (Let(x, et, stage1, ctx.quote(rt), ev, eb), rt, vstage2)

      case S.Pi(x, Impl, a, b) =>
        val ea = checkType(a, SMeta)
        val eb = checkType(b, SMeta)(ctx.bind(x, ctx.eval(ea), SMeta))
        (Pi(x, Impl, ea, eb), VU(SMeta), SMeta)
      case S.Pi(x, _, a, b) =>
        val (ea, s) = inferType(a)
        s match
          case SMeta =>
            val eb = checkType(b, SMeta)(ctx.bind(x, ctx.eval(ea), SMeta))
            (Pi(x, Expl, ea, eb), VU(SMeta), SMeta)
          case STy(rvf) =>
            unify(rvf, VVal)
            val vf = newVF()
            val eb = checkType(b, STy(ctx.eval(vf)))
            (TFun(ea, vf, eb), VFTy(), SMeta)

      case S.Lam(x, S.ArgIcit(Impl), mty, b) =>
        val pty = mty match
          case Some(ty) =>
            val ety = checkType(ty, SMeta)
            ctx.eval(ety)
          case None =>
            val m = newMeta(VU(SMeta), SMeta)
            ctx.eval(m)
        val ctx2 = ctx.bind(x, pty, SMeta)
        val (eb, rty) = insert(SMeta, infer(b, SMeta)(ctx2))(ctx2)
        val fty = VPi(x, Impl, pty, ctx.close(rty))
        (Lam(x, Impl, ctx.quote(fty), eb), fty, SMeta)
      case S.Lam(x, S.ArgIcit(Expl), mty, b) =>
        val (pty, s) = mty match
          case Some(ty) =>
            val (ety, s) = inferType(ty)
            (ctx.eval(ety), s)
          case None => error(s"cannot infer unannotated lambda: $tm")
        s match
          case SMeta =>
            val ctx2 = ctx.bind(x, pty, SMeta)
            val (eb, rty) = insert(SMeta, infer(b, SMeta)(ctx2))(ctx2)
            val fty = VPi(x, Expl, pty, ctx.close(rty))
            (Lam(x, Expl, ctx.quote(fty), eb), fty, SMeta)
          case STy(rvf) =>
            unify(rvf, VVal)
            val ctx2 = ctx.bind(x, pty, s)
            val vf = ctx.eval(newVF())
            val rty0 = ctx.eval(newMeta(VUTy(vf), SMeta))
            val eb0 = check(b, rty0, STy(vf))(ctx2)
            val (eb, rty) = insert(STy(vf), (eb0, rty0))(ctx2)
            val fty = VTFun(pty, vf, rty)
            (Lam(x, Expl, ctx.quote(fty), eb), fty, STy(vf))
      case S.Lam(_, S.ArgNamed(_), _, _) => error(s"cannot infer: $tm")

      case S.App(f, a, i) =>
        val (icit, ef, fty, st) = i match
          case S.ArgNamed(x) =>
            val (ef, fty, st) = insertPi(infer(f), Until(x))
            (Impl, ef, fty, st)
          case S.ArgIcit(Impl) =>
            val (ef, fty, st) = infer(f)
            (Impl, ef, fty, st)
          case S.ArgIcit(Expl) =>
            val (ef, fty, st) = insertPi(infer(f))
            (Expl, ef, fty, st)
        force(fty) match
          case VPi(x, icit2, pty, rty) =>
            if icit != icit2 then error(s"icit mismatch: $tm")
            val ea = check(a, pty, SMeta)
            (App(ef, ea, icit), rty(ctx.eval(ea)), SMeta)
          case VTFun(pty, rvf, rty) =>
            if icit == Impl then error(s"implicit app in Ty: $tm")
            val ea = check(a, pty, SVTy())
            (App(ef, ea, icit), rty, STy(rvf))
          case _ =>
            st match
              case SMeta =>
                val pty = ctx.eval(newMeta(VU(SMeta), SMeta))
                val x = DoBind(Name("x"))
                val rty =
                  CClos(
                    ctx.env,
                    newMeta(VU(SMeta), SMeta)(ctx.bind(x, pty, SMeta))
                  )
                val ef2 = coe(ef, fty, SMeta, VPi(x, icit, pty, rty), SMeta)
                val ea = check(a, pty, SMeta)
                (App(ef2, ea, icit), rty(ctx.eval(ea)), SMeta)
              case STy(svf) =>
                if icit == Impl then error(s"implicit app in Ty: $tm")
                unify(svf, VFun)
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rvf = ctx.eval(newVF())
                val rty = ctx.eval(newMeta(VUTy(rvf), SMeta))
                val ef2 = coe(ef, fty, st, VTFun(pty, rvf, rty), st)
                val ea = check(a, pty, SVTy())
                (App(ef2, ea, Expl), rty, STy(rvf))

      case S.Fix(g, x, b, arg) =>
        val (earg, vty) = infer(arg, SVTy())
        val vf = ctx.eval(newVF())
        val rty = newMeta(VUTy(vf), SMeta)
        val vrty = ctx.eval(rty)
        val ft = VTFun(vty, vf, vrty)
        val eb =
          check(b, vrty, STy(vf))(ctx.bind(g, ft, SFTy()).bind(x, vty, SVTy()))
        (Fix(ctx.quote(vty), rty, g, x, eb, earg), vrty, STy(vf))

      case S.Lift(a) =>
        val vf = newVF()
        val vvf = ctx.eval(vf)
        val ea = checkType(a, STy(vvf))
        (Lift(vf, ea), VU(SMeta), SMeta)
      case S.Quote(t) =>
        val vf = ctx.eval(newVF())
        val (et, a) = infer(t, STy(vf))
        (et.quote, VLift(vf, a), SMeta)
      case S.Splice(t) =>
        val (et, a) = infer(t, SMeta)
        val vf = ctx.eval(newVF())
        val (et2, a2) = adjustStage(et, a, SMeta, STy(vf))
        (et2, a2, STy(vf))

  // elaboration
  private def prettyHoles(implicit ctx0: Ctx): String =
    holes.toList
      .map((x, e) =>
        e match
          case HoleEntry(ctx, tm, vty, s) =>
            s"_$x : ${ctx.pretty(vty)} : ${ctx.pretty(s)} = ${ctx
                .pretty(tm)}\nlocals:\n${ctx.prettyLocals}"
      )
      .mkString("\n\n")

  private def elaborate(tm: S.Tm, ty: Option[S.Ty], meta: Boolean)(implicit
      ctx: Ctx
  ): (Tm, Ty, CStage) =
    resetMetas()
    holes.clear()

    val vstage = if meta then SMeta else STy(ctx.eval(newVF()))
    val (etm_, ety_, _) = check(tm, ty, vstage)
    val etm = ctx.zonk(etm_)
    val ety = ctx.zonk(ety_)
    val estage = ctx.zonk(vstage)

    debug(
      s"elaborated ${ctx.pretty(etm)} : ${ctx.pretty(ety)} : ${ctx.prettyS(estage)}"
    )
    if holes.nonEmpty then
      error(
        s"holes found: ${ctx.pretty(etm)} : ${ctx.pretty(ety)} : ${ctx
            .prettyS(estage)}\n\n${prettyHoles}"
      )
    val ums = unsolvedMetas()
    if ums.nonEmpty then
      error(
        s"unsolved metas: ${ctx.pretty(etm)} : ${ctx
            .pretty(ety)}\n${ums
            .map((id, ty, s) => s"?$id : ${ctx.pretty(ty)} : $s")
            .mkString("\n")}"
      )
    (etm, ety, estage)

  private def elaborate(module: String, d: S.Def): List[Def] =
    debug(s"elaborate $module $d")
    d match
      case S.DImport(_, _, _, false, Nil) => Nil
      case S.DImport(pos, false, m, all, xs0) =>
        implicit val ctx: Ctx = Ctx.empty(module, pos)
        val xs = if all then allNamesFromModule(m) else xs0
        xs.foreach { x =>
          getGlobal(m, x) match
            case None => error(s"module $m does not contain $x")
            case Some(e) =>
              imported.get(x) match
                case Some(_) => error(s"$x is already imported")
                case None    => imported += (x -> (m, x))
        }
        Nil
      case S.DImport(pos, true, m, all, xs0) =>
        implicit val ctx: Ctx = Ctx.empty(module, pos)
        val xs = if all then allNamesFromModule(m) else xs0
        xs.map { x =>
          getGlobal(m, x) match
            case None => error(s"module $m does not contain $x")
            case Some(e) =>
              setGlobal(e.copy(module = module))
              DDef(module, x, e.ty, e.stage, e.tm)
        }
      case S.DDef(pos, x, m, t, v) =>
        implicit val ctx: Ctx = Ctx.empty(module, pos)
        if getGlobal(module, x).isDefined then error(s"duplicate global $x")
        val (etm, ety, estage) = elaborate(v, t, m)
        setGlobal(
          GlobalEntry(
            module,
            x,
            etm,
            ety,
            estage,
            ctx.eval(etm),
            ctx.eval(ety),
            ctx.eval(estage)
          )
        )
        val ed = DDef(module, x, ety, estage, etm)
        debug(s"elaborated $ed")
        List(ed)
      case S.DData(pos, x, ps, cs) => impossible()

  def elaborate(module: String, uri: String, ds: S.Defs): Defs =
    imported.clear()
    try Defs(ds.toList.flatMap(d => elaborate(module, d)))
    catch case e: ElaborateError => throw ElaborateError(e.pos, uri, e.msg)
