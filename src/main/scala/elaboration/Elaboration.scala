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
  final case class ElaborateError(pos: PosInfo, msg: String)
      extends Exception(msg)

  private def error(msg: String)(implicit ctx: Ctx): Nothing =
    throw ElaborateError(ctx.pos, msg)

  // unification
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
      stage: Stage
  )
  private val holes: mutable.Map[Name, HoleEntry] = mutable.Map.empty

  // metas
  private def newMeta(ty: VTy, s: Stage)(implicit ctx: Ctx): Tm = force(
    ty
  ) match
    case VUnitType() => Prim(PUnit)
    case _ =>
      val closed = ctx.closeVTy(ty)
      val m = freshMeta(closed, s)
      debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
      AppPruning(Meta(m), ctx.pruning)

  private enum InsertMode:
    case All
    case Until(name: Name)
  import InsertMode.*

  private def insertPi(inp: (Tm, VTy, Stage), mode: InsertMode = All)(implicit
      ctx: Ctx
  ): (Tm, VTy, Stage) =
    @tailrec
    def go(tm: Tm, ty: VTy, st: Stage): (Tm, VTy, Stage) =
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

  private def insert(inp: (Tm, VTy, Stage))(implicit
      ctx: Ctx
  ): (Tm, VTy, Stage) =
    inp._1 match
      case Lam(_, Impl, _, _) => inp
      case _                  => insertPi(inp)

  private def insert(s: Stage, inp: (Tm, VTy))(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    val res = insert((inp._1, inp._2, s))
    (res._1, res._2)

  // coercion
  private def tryAdjustStage(t: Tm, a: VTy, s1: Stage, s2: Stage)(implicit
      ctx: Ctx
  ): Option[(Tm, VTy)] = (s1, s2) match
    case (SMeta, SMeta) => None
    case (STy, STy)     => None
    case (STy, SMeta)   => Some((t.quote, VLift(a)))
    case (SMeta, STy) =>
      debug(s"$t : ${ctx.pretty(a)} : $s1 to $s2")
      val m = ctx.eval(newMeta(VTy(), SMeta))
      unify(a, VLift(m))
      Some((t.splice, m))

  private def adjustStage(t: Tm, a: VTy, s1: Stage, s2: Stage)(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    debug(
      s"adjustStage $t : ${ctx.pretty(a)} : $s1 to $s2"
    )
    tryAdjustStage(t, a, s1, s2).fold((t, a))(x => x)

  private def coe(t: Tm, a: VTy, st1: Stage, b: VTy, st2: Stage)(implicit
      ctx: Ctx
  ): Tm =
    debug(
      s"coeTop ${ctx.pretty(t)} : ${ctx.pretty(a)} : $st1 to ${ctx.pretty(b)} : $st2"
    )
    def pick(x: Bind, y: Bind)(implicit ctx: Ctx): Bind = ctx.fresh((x, y) match
      case (DontBind, DontBind) => DoBind(Name("x"))
      case (DontBind, x)        => x
      case (x, DontBind)        => x
      case (_, x)               => x
    )
    def justAdjust(t: Tm, a: VTy, st1: Stage, b: VTy, st2: Stage)(implicit
        ctx: Ctx
    ): Option[Tm] =
      tryAdjustStage(t, a, st1, st2) match
        case None         => unify(a, b); None
        case Some((t, a)) => unify(a, b); Some(t)
    def go(
        t: Tm,
        a: VTy,
        st1: Stage,
        b: VTy,
        st2: Stage
    )(implicit ctx: Ctx): Option[Tm] =
      debug(
        s"coe ${ctx.pretty(t)} : ${ctx.pretty(a)} : $st1 to ${ctx.pretty(b)} : $st2"
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
              body.map(Lam(x, i, ctx.quote(b), _))
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

        case (VSigma(x, p1, r1), VSigma(x2, p2, r2)) =>
          val fst = go(Proj(t, Fst, Irrelevant), p1, SMeta, p2, SMeta)
          val f = vfst(ctx.eval(t))
          val snd = fst match
            case None =>
              go(Proj(t, Snd, Irrelevant), r1(f), SMeta, r2(f), SMeta)
            case Some(fst) =>
              go(
                Proj(t, Snd, Irrelevant),
                r1(f),
                SMeta,
                r2(ctx.eval(fst)),
                SMeta
              )
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(Pair(fst, Proj(t, Snd, Irrelevant), ctx.quote(b)))
            case (None, Some(snd)) =>
              Some(Pair(Proj(t, Fst, Irrelevant), snd, ctx.quote(b)))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))

        case (VFun(p1, r1), VFun(p2, r2)) =>
          val x = DoBind(Name("x"))
          val ctx2 = ctx.bind(x, VVal(p2), STy)
          go(Var(ix0), VVal(p2), STy, VVal(p1), STy)(ctx2) match
            case None =>
              val body =
                go(App(Wk(t), Var(ix0), Expl), r1, STy, r2, STy)(ctx2)
              body.map(Lam(x, Expl, ctx.quote(b), _))
            case Some(coev0) =>
              go(App(Wk(t), coev0, Expl), r1, STy, r2, STy)(ctx2) match
                case None =>
                  Some(Lam(x, Expl, ctx.quote(b), App(Wk(t), coev0, Expl)))
                case Some(body) => Some(Lam(x, Expl, ctx.quote(b), body))

        case (VPairTy(p1, r1), VPairTy(p2, r2)) =>
          val fst =
            go(Proj(t, Fst, ctx.quote(p1)), VVal(p1), STy, VVal(p2), STy)
          val snd =
            go(Proj(t, Snd, ctx.quote(r1)), VVal(r1), STy, VVal(r2), STy)
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(Pair(fst, Proj(t, Snd, ctx.quote(r1)), ctx.quote(b)))
            case (None, Some(snd)) =>
              Some(Pair(Proj(t, Fst, ctx.quote(p1)), snd, ctx.quote(b)))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))

        case (VFun(p1, r1), VPi(x, i, p2, r2)) =>
          if i == Impl then
            error(s"coerce error ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          val ctx2 = ctx.bind(x, p2, SMeta)
          go(Var(ix0), p2, SMeta, VVal(p1), STy)(ctx2) match
            case None =>
              val body =
                go(
                  App(Wk(t), Var(ix0), i),
                  r1,
                  STy,
                  r2(VVar(ctx.lvl)),
                  SMeta
                )(
                  ctx2
                )
              body.map(Lam(x, i, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i),
                r1,
                STy,
                r2(VVar(ctx.lvl)),
                SMeta
              )(ctx2) match
                case None => Some(Lam(x, i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(x, i, ctx.quote(b), body))
        case (VPi(x, i, p1, r1), VFun(p2, r2)) =>
          if i == Impl then
            error(s"coerce error ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          val ctx2 = ctx.bind(x, VVal(p2), STy)
          go(Var(ix0), VVal(p2), STy, p1, SMeta)(ctx2) match
            case None =>
              val body =
                go(
                  App(Wk(t), Var(ix0), i),
                  r1(VVar(ctx.lvl)),
                  SMeta,
                  r2,
                  STy
                )(
                  ctx2
                )
              body.map(Lam(x, i, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i),
                r1(ctx2.eval(coev0)),
                SMeta,
                r2,
                STy
              )(ctx2) match
                case None => Some(Lam(x, i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(x, i, ctx.quote(b), body))

        case (VPairTy(p1, r1), VSigma(_, p2, r2)) =>
          val fst = go(Proj(t, Fst, ctx.quote(p1)), VVal(p1), STy, p2, SMeta)
          val snd = fst match
            case None =>
              go(
                Proj(t, Snd, ctx.quote(r1)),
                VVal(r1),
                STy,
                r2(vfst(ctx.eval(t))),
                SMeta
              )
            case Some(fst) =>
              go(
                Proj(t, Snd, ctx.quote(r1)),
                VVal(r1),
                STy,
                r2(ctx.eval(fst)),
                SMeta
              )
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(Pair(fst, Proj(t, Snd, ctx.quote(r1)), ctx.quote(b)))
            case (None, Some(snd)) =>
              Some(Pair(Proj(t, Fst, ctx.quote(p1)), snd, ctx.quote(b)))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))
        case (VSigma(_, p1, r1), VPairTy(p2, r2)) =>
          val fst = go(Proj(t, Fst, Irrelevant), p1, SMeta, VVal(p2), STy)
          val f = vfst(ctx.eval(t))
          val snd = fst match
            case None =>
              go(Proj(t, Snd, Irrelevant), r1(f), SMeta, VVal(r2), STy)
            case Some(fst) =>
              go(Proj(t, Snd, Irrelevant), r1(f), SMeta, VVal(r2), STy)
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(Pair(fst, Proj(t, Snd, Irrelevant), ctx.quote(b)))
            case (None, Some(snd)) =>
              Some(Pair(Proj(t, Fst, Irrelevant), snd, ctx.quote(b)))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))

        case (VU(STy), VU(SMeta)) => Some(Lift(t))
        case (VVTy(), VU(STy))    => Some(t.embedVal)
        case (VVTy(), VU(SMeta))  => Some(Lift(t.embedVal))
        case (VLift(a), VLift(b)) => unify(a, b); None
        case (VLift(a), b)        => Some(coe(t.splice, a, STy, b, st2))
        case (a, VLift(b))        => Some(coe(t, a, st1, b, STy).quote)
        case _                    => justAdjust(t, a, st1, b, st2)
    go(t, a, st1, b, st2).getOrElse(t)

  // elaboration
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

  private def checkType(ty: S.Ty, s: Stage)(implicit ctx: Ctx): Tm =
    check(ty, VU(s), SMeta)

  private def checkVTy(ty: S.Ty)(implicit ctx: Ctx): Tm =
    check(ty, VVTy(), SMeta)

  private def check(tm: S.Tm, ty: Option[S.Ty], stage: Stage)(implicit
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

  private def check(tm: S.Tm, ty: VTy, stage: Stage)(implicit
      ctx: Ctx
  ): Tm =
    if !tm.isPos then debug(s"check $tm : ${ctx.pretty(ty)} : $stage")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty, stage)(ctx.enter(pos))

      case (S.Lam(x, i, ot, b), VPi(y, i2, a, rt)) if icitMatch(i, y, i2) =>
        ot.foreach(t0 => {
          val ety = checkType(t0, SMeta)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, ctx.inst(rt), SMeta)(ctx.bind(x, a, SMeta))
        Lam(x, i2, ctx.quote(ty), eb)
      case (S.Lam(x, S.ArgIcit(Expl), ot, b), VFun(a, rt)) =>
        ot.foreach(t0 => {
          val ety = checkVTy(t0)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, rt, STy)(ctx.bind(x, VVal(a), STy))
        Lam(x, Expl, ctx.quote(ty), eb)
      case (S.Var(x), VPi(_, Impl, _, _)) if hasMetaType(x) =>
        val Some((ix, varty, SMeta)) = ctx.lookup(x): @unchecked
        unify(varty, ty)
        Var(ix)
      case (tm, VPi(x, Impl, a, b)) =>
        val etm = check(tm, ctx.inst(b), SMeta)(ctx.bind(x, a, SMeta, true))
        Lam(x, Impl, ctx.quote(ty), etm)

      case (S.Pair(fst, snd), VSigma(_, a, b)) =>
        val efst = check(fst, a, SMeta)
        val esnd = check(snd, b(ctx.eval(efst)), SMeta)
        Pair(efst, esnd, ctx.quote(ty))
      case (S.Pair(fst, snd), VPairTy(a, b)) =>
        val efst = check(fst, VVal(a), STy)
        val esnd = check(snd, VVal(b), STy)
        Pair(efst, esnd, ctx.quote(ty))

      case (S.Lift(a), VU(SMeta)) => Lift(checkType(a, STy))

      case (S.Pi(x, i, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Pi(x, i, ea, eb)
      case (S.Pi(x, Expl, a, b), VU(STy)) =>
        val ea = checkVTy(a)
        val eb = checkType(b, STy)
        tFun(ea, eb)
      case (S.Sigma(x, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Sigma(x, ea, eb)
      case (S.Sigma(x, a, b), VU(STy)) =>
        val ea = checkVTy(a)
        val eb = checkVTy(b)
        tPair(ea, eb).embedVal

      case (S.Quote(t), VLift(a)) => check(t, a, STy).quote
      case (t, VLift(a))          => check(t, a, STy).quote

      case (S.Let(x, m, t, v, b), _) if stage == (if m then SMeta else STy) =>
        val (ev, et, vt) = check(v, t, stage)
        val eb = check(b, ty, stage)(
          ctx.define(x, vt, et, stage, ctx.eval(ev), ev)
        )
        Let(x, et, stage, ctx.quote(ty), ev, eb)

      case (S.Fix(go, x, b, a), _) if stage == STy =>
        val ta = newMeta(VVTy(), SMeta)
        val vta = ctx.eval(ta)
        val ea = check(a, VVal(vta), STy)
        val fun = VFun(vta, ty)
        val eb = check(b, ty, STy)(
          ctx.bind(DoBind(go), fun, STy).bind(DoBind(x), VVal(vta), STy)
        )
        Fix(go, x, ctx.quote(fun), eb, ea)

      case (S.Hole(ox), _) =>
        val t = newMeta(ty, stage)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty, stage))
        t

      case (t, VFlex(_, _)) =>
        val (etm, vt) = insert(stage, infer(t, stage))
        coe(etm, vt, stage, ty, stage)
      case _ =>
        val (etm, ty2, stage2) = insert(infer(tm))
        coe(etm, ty2, stage2, ty, stage)

  private def projIndex(tm: Val, x: Bind, ix: Int, clash: Boolean): Val =
    x match
      case DoBind(x) if !clash => vproj(tm, Named(Some(x), ix))
      case _ =>
        @tailrec
        def go(tm: Val, ix: Int): Val = ix match
          case 0 => vproj(tm, Fst)
          case n => go(vproj(tm, Snd), n - 1)
        go(tm, ix)
  private def projNamed(tm: Val, ty: VTy, x: Name)(implicit
      ctx: Ctx
  ): (ProjType, VTy) =
    @tailrec
    def go(ty: VTy, ix: Int, ns: Set[Name]): (ProjType, VTy) =
      force(ty) match
        case VSigma(DoBind(y), fstty, _) if x == y =>
          (Named(Some(x), ix), fstty)
        case VSigma(y, _, sndty) =>
          val (clash, newns) = y match
            case DoBind(y) => (ns.contains(y), ns + y)
            case DontBind  => (false, ns)
          go(sndty(projIndex(tm, y, ix, clash)), ix + 1, newns)
        case _ =>
          throw error(
            s"expected sigma in named projection .$x, got ${ctx.pretty(ty)}"
          )
    go(ty, 0, Set.empty)

  private def inferType(ty: S.Ty)(implicit ctx: Ctx): (Tm, Stage) =
    val (t, a) = infer(ty, SMeta)
    force(a) match
      case VU(s) => (t, s)
      case ty    => error(s"expected type got ${ctx.pretty(ty)}")

  private def infer(tm: S.Tm, s: Stage)(implicit ctx: Ctx): (Tm, VTy) =
    if !tm.isPos then debug(s"infer $tm : $s")
    tm match
      case S.Pos(pos, tm) => infer(tm, s)(ctx.enter(pos))

      case S.Lam(x, S.ArgIcit(i), ot, b) =>
        val (sa, sb) = s match
          case SMeta => (SMeta, SMeta)
          case STy =>
            if i == Impl then error(s"implicit lambda cannot be in Ty: $tm")
            (STy, STy)
        val a = ot match
          case None     => newMeta(VU(sa), SMeta)
          case Some(ty) => checkType(ty, sa)
        val va = ctx.eval(a)
        val (eb, rt) = infer(b, sb)(ctx.bind(x, va, sa))
        val fun = sb match
          case SMeta => VPi(x, i, va, ctx.close(rt))
          case STy   => VFun(va, rt)
        (Lam(x, i, ctx.quote(fun), eb), fun)
      case S.Lam(x, S.ArgNamed(_), _, _) => error(s"cannot infer $tm")

      case S.Pair(fst, snd) =>
        val (efst, fty) = infer(fst, s)
        val (esnd, sty) = infer(snd, s)
        val ty = s match
          case SMeta => vsigma("_", fty, _ => sty)
          case STy   => VPairTy(fty, sty)
        (Pair(efst, esnd, ctx.quote(ty)), ty)

      case S.Hole(ox) =>
        val ty = ctx.eval(newMeta(VU(s), SMeta))
        val t = newMeta(ty, s)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty, s))
        (t, ty)

      case S.Fix(go, x, b, a) if s == STy =>
        val ta = newMeta(VVTy(), SMeta)
        val vta = ctx.eval(ta)
        val ea = check(a, VVal(vta), STy)
        val rt = ctx.eval(newMeta(VU(STy), SMeta))
        val fun = VFun(vta, rt)
        val eb = check(b, rt, STy)(
          ctx.bind(DoBind(go), fun, STy).bind(DoBind(x), VVal(vta), STy)
        )
        (Fix(go, x, ctx.quote(fun), eb, ea), rt)

      case _ =>
        val (t, a, si) = insert(infer(tm))
        debug(
          s"inferred $t : ${ctx.pretty(a)} : $si to $s"
        )
        adjustStage(t, a, si, s)

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, Stage) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))
      case S.IntLit(n)    => (IntLit(n), VVal(VInt()), STy)
      case S.U(SMeta)     => (U(SMeta), VU(SMeta), SMeta)
      case S.U(STy)       => (U(STy), VU(SMeta), SMeta)
      case S.Var(x) =>
        PrimName(x) match
          case Some(p) =>
            val (t, u) = primType(p)
            (Prim(p), t, u)
          case None =>
            ctx.lookup(x) match
              case Some((ix, ty, u)) => (Var(ix), ty, u)
              case None =>
                getGlobal(x) match
                  case Some(e) => (Global(x), e.vty, e.stage)
                  case None    => error(s"undefined variable $x")
      case S.Let(x, m, t, v, b) =>
        val stage = if m then SMeta else STy
        val (ev, et, vt) = check(v, t, stage)
        val (eb, rt) =
          infer(b, stage)(ctx.define(x, vt, et, stage, ctx.eval(ev), ev))
        (Let(x, et, stage, ctx.quote(rt), ev, eb), rt, stage)

      case S.Fix(go, x, b, a) =>
        val ta = newMeta(VVTy(), SMeta)
        val vta = ctx.eval(ta)
        val ea = check(a, VVal(vta), STy)
        val rt = ctx.eval(newMeta(VU(STy), SMeta))
        val fun = VFun(vta, rt)
        val eb = check(b, rt, STy)(
          ctx.bind(DoBind(go), fun, STy).bind(DoBind(x), VVal(vta), STy)
        )
        (Fix(go, x, ctx.quote(fun), eb, ea), rt, STy)

      case S.Hole(ox) => error(s"cannot infer hole $tm")

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
          case STy =>
            ea match
              case App(Prim(PVal), ea1, Expl) =>
                val eb = checkType(b, STy)
                (tFun(ea1, eb), VU(STy), SMeta)
              case _ => error(s"Fun parameter should be in ValTy")

      case S.Sigma(x, a, b) =>
        val (ea, s) = inferType(a)
        s match
          case SMeta =>
            val eb = checkType(b, SMeta)(ctx.bind(x, ctx.eval(ea), SMeta))
            (Sigma(x, ea, eb), VU(SMeta), SMeta)
          case STy =>
            val eb = checkType(b, STy)
            (ea, eb) match
              case (App(Prim(PVal), ea1, Expl), App(Prim(PVal), eb1, Expl)) =>
                (
                  App(App(Prim(PPair), ea1, Expl), eb1, Expl).embedVal,
                  VU(STy),
                  SMeta
                )
              case _ => error(s"Pair parameters should be in ValTy")

      case S.Pair(fst, snd) =>
        val (efst, fstty, s1) = infer(fst)
        s1 match
          case SMeta =>
            val (esnd, sndty) = infer(snd, SMeta)
            val ty = VSigma(DontBind, fstty, CFun(_ => sndty))
            (
              Pair(efst, esnd, ctx.quote(ty)),
              ty,
              SMeta
            )
          case STy =>
            fstty match
              case VVal(vfstty) =>
                val ta = newMeta(VVTy(), SMeta)
                val vta = ctx.eval(ta)
                val esnd = check(snd, vta, STy)
                val ty = VPairTy(vfstty, vta)
                (
                  Pair(efst, esnd, ctx.quote(ty)),
                  ty,
                  STy
                )
              case _ => error(s"pair elements must be in VTy")

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
          case STy =>
            pty match
              case VVal(ta) =>
                val ctx2 = ctx.bind(x, pty, s)
                val (eb, rty) = insert(STy, infer(b, STy)(ctx2))(ctx2)
                val fty = VFun(ta, rty)
                (Lam(x, Expl, ctx.quote(fty), eb), fty, STy)
              case _ => error(s"lambda parameter needs to be in VTy")
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
          case VFun(pty, rty) =>
            if icit == Impl then error(s"implicit app in Ty: $tm")
            val ea = check(a, VVal(pty), STy)
            (App(ef, ea, icit), rty, STy)
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
              case STy =>
                if icit == Impl then error(s"implicit app in Ty: $tm")
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rty = ctx.eval(newMeta(VU(STy), SMeta))
                val ef2 = coe(ef, fty, st, VFun(pty, rty), st)
                val ea = check(a, VVal(pty), STy)
                (App(ef2, ea, Expl), rty, STy)

      case S.Proj(t, p) =>
        val (et, ty, st) = insertPi(infer(t))
        (force(ty), p) match
          case (_, S.Named(x)) =>
            if st != SMeta then error(s"can only do named projection in Meta")
            val (p, pty) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p, ctx.quote(pty)), pty, SMeta)
          case (VSigma(_, fstty, _), S.Fst) =>
            (Proj(et, Fst, ctx.quote(fstty)), fstty, SMeta)
          case (VSigma(_, _, sndty), S.Snd) =>
            val rt = sndty(vfst(ctx.eval(et)))
            (Proj(et, Snd, ctx.quote(rt)), rt, SMeta)
          case (VPairTy(fstty, _), S.Fst) =>
            (Proj(et, Fst, ctx.quote(fstty)), VVal(fstty), STy)
          case (VPairTy(_, sndty), S.Snd) =>
            (Proj(et, Snd, ctx.quote(sndty)), VVal(sndty), STy)
          case (tty, _) =>
            st match
              case SMeta =>
                val pty = ctx.eval(newMeta(VU(SMeta), SMeta))
                val x = DoBind(Name("x"))
                val rty =
                  CClos(
                    ctx.env,
                    newMeta(VU(SMeta), SMeta)(ctx.bind(x, pty, SMeta))
                  )
                val et2 = coe(et, tty, SMeta, VSigma(x, pty, rty), SMeta)
                p match
                  case S.Fst => (Proj(et2, Fst, ctx.quote(pty)), pty, SMeta)
                  case S.Snd =>
                    val ty = rty(vfst(ctx.eval(et2)))
                    (Proj(et2, Snd, ctx.quote(ty)), ty, SMeta)
                  case _ => error(s"named projection with ambigious type: $tm")
              case STy =>
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rty = ctx.eval(newMeta(VVTy(), SMeta))
                val et2 = coe(et, tty, STy, VVal(VPairTy(pty, rty)), STy)
                p match
                  case S.Fst => (Proj(et2, Fst, ctx.quote(pty)), VVal(pty), STy)
                  case S.Snd => (Proj(et2, Snd, ctx.quote(rty)), VVal(rty), STy)
                  case _ => error(s"named projection with ambigious type: $tm")

      case S.Lift(a) =>
        val ea = checkType(a, STy)
        (Lift(ea), VU(SMeta), SMeta)
      case S.Quote(t) =>
        val (et, a) = infer(t, STy)
        (et.quote, VLift(a), SMeta)
      case S.Splice(t) =>
        val (et, a) = infer(t, SMeta)
        val (et2, a2) = adjustStage(et, a, SMeta, STy)
        (et2, a2, STy)

  private def prettyHoles(implicit ctx0: Ctx): String =
    holes.toList.reverse
      .map((x, e) =>
        e match
          case HoleEntry(ctx, tm, vty, s) =>
            s"_$x : ${ctx.pretty(vty)} : $s = ${ctx.pretty(tm)}\nlocals:\n${ctx.prettyLocals}"
      )
      .mkString("\n\n")

  private def elaborate(tm: S.Tm, ty: Option[S.Ty], meta: Boolean)(implicit
      ctx: Ctx
  ): (Tm, Ty, Stage) =
    resetMetas()
    holes.clear()

    val stage = if meta then SMeta else STy
    val (etm_, ety_, _) = check(tm, ty, stage)
    val etm = ctx.zonk(etm_)
    val ety = ctx.zonk(ety_)

    debug(
      s"elaborated ${ctx.pretty(etm)} : ${ctx.pretty(ety)} : $stage}"
    )
    if holes.nonEmpty then
      error(
        s"holes found: ${ctx.pretty(etm)} : ${ctx.pretty(ety)} : $stage\n\n${prettyHoles}"
      )
    val ums = unsolvedMetas()
    if ums.nonEmpty then
      error(
        s"unsolved metas: ${ctx.pretty(etm)} : ${ctx
            .pretty(ety)}\n${ums
            .map((id, ty, s) => s"?$id : ${ctx.pretty(ty)} : $s")
            .mkString("\n")}"
      )
    (etm, ety, stage)

  def elaborate(d: S.Def): Def =
    debug(s"elaborate $d")
    d match
      case S.DDef(x, m, t, v) =>
        implicit val ctx: Ctx = Ctx.empty()
        if getGlobal(x).isDefined then error(s"duplicate global $x")
        val (etm, ety, estage) = elaborate(v, t, m)
        setGlobal(
          GlobalEntry(
            x,
            etm,
            ety,
            estage,
            ctx.eval(etm),
            ctx.eval(ety)
          )
        )
        val ed = DDef(x, ety, estage, etm)
        debug(s"elaborated $ed")
        ed

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
