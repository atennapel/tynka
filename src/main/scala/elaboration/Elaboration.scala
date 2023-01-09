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
  private def unify(a: Stage[VTy], b: Stage[VTy])(implicit ctx: Ctx): Unit =
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
      stage: Stage[VTy]
  )
  private val holes: mutable.Map[Name, HoleEntry] = mutable.Map.empty

  // metas
  private def newMeta(ty: VTy, s: Stage[VTy])(implicit ctx: Ctx): Tm = force(
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

  private def insertPi(inp: (Tm, VTy, Stage[VTy]), mode: InsertMode = All)(
      implicit ctx: Ctx
  ): (Tm, VTy, Stage[VTy]) =
    @tailrec
    def go(tm: Tm, ty: VTy, st: Stage[VTy]): (Tm, VTy, Stage[VTy]) = force(
      ty
    ) match
      case VPi(y, Impl, a, b) =>
        mode match
          case Until(x) if x == y => (tm, ty, st)
          case _ =>
            val m = newMeta(a, st)
            val mv = ctx.eval(m)
            go(App(tm, m, Impl), b(mv), st)
      case _ =>
        mode match
          case Until(x) => error(s"no implicit pi found with parameter $x")
          case _        => (tm, ty, st)
    go(inp._1, inp._2, inp._3)

  private def insert(inp: (Tm, VTy, Stage[VTy]))(implicit
      ctx: Ctx
  ): (Tm, VTy, Stage[VTy]) =
    inp._1 match
      case Lam(_, Impl, _) => inp
      case _               => insertPi(inp)

  private def insert(s: Stage[VTy], inp: (Tm, VTy))(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    val res = insert((inp._1, inp._2, s))
    (res._1, res._2)

  // coercion
  private def tryAdjustStage(t: Tm, a: VTy, s1: Stage[VTy], s2: Stage[VTy])(
      implicit ctx: Ctx
  ): Option[(Tm, VTy)] = (s1, s2) match
    case (S1, S1)       => None
    case (S0(a), S0(b)) => unify(a, b); None
    case (S0(vf), S1)   => Some((t.quote, VLift(vf, a)))
    case (S1, S0(vf)) =>
      val m = ctx.eval(newMeta(VU(s2), S1))
      unify(a, VLift(vf, m))
      Some((t.splice, m))

  private def adjustStage(t: Tm, a: VTy, s1: Stage[VTy], s2: Stage[VTy])(
      implicit ctx: Ctx
  ): (Tm, VTy) = tryAdjustStage(t, a, s1, s2).fold((t, a))(x => x)

  private def coe(t: Tm, a: VTy, st1: Stage[VTy], b: VTy, st2: Stage[VTy])(
      implicit ctx: Ctx
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
    def justAdjust(t: Tm, a: VTy, st1: Stage[VTy], b: VTy, st2: Stage[VTy])(
        implicit ctx: Ctx
    ): Option[Tm] =
      tryAdjustStage(t, a, st1, st2) match
        case None         => unify(st1, st2); unify(a, b); None
        case Some((t, a)) => unify(a, b); Some(t)
    def go(
        t: Tm,
        a: VTy,
        st1: Stage[VTy],
        b: VTy,
        st2: Stage[VTy]
    )(implicit ctx: Ctx): Option[Tm] =
      debug(
        s"coe ${ctx.pretty(t)} : ${ctx.pretty(a)} : ${ctx.pretty(st1)} to ${ctx
            .pretty(b)} : ${ctx.pretty(st2)}"
      )
      (force(a), force(b)) match
        case (VPi(x, i, p1, r1), VPi(x2, i2, p2, r2)) =>
          if i == i2 then
            error(
              s"plicity mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          val ctx2 = ctx.bind(x, p2, st2)
          val coev0 = go(Var(ix0), p2, st2, p1, st1)
          coev0 match
            case None =>
              val v = VVar(ctx.lvl)
              val body =
                go(App(Wk(t), Var(ix0), i), r1(v), st1, r2(v), st2)(ctx2)
              body.map(Lam(x, i, _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i),
                r1(ctx2.eval(coev0)),
                st1,
                r2(VVar(ctx.lvl)),
                st2
              )(ctx2) match
                case None => Some(Lam(pick(x, x2), i, App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(pick(x, x2), i, body))

        case (VSigma(x, p1, r1), VSigma(x2, p2, r2)) =>
          val fst = go(Proj(t, Fst), p1, st1, p2, st2)
          val f = vfst(ctx.eval(t))
          val snd = fst match
            case None => go(Proj(t, Snd), r1(f), st1, r2(f), st2)
            case Some(fst) =>
              go(Proj(t, Snd), r1(f), st1, r2(ctx.eval(fst)), st2)
          (fst, snd) match
            case (None, None)           => None
            case (Some(fst), None)      => Some(Pair(fst, Proj(t, Snd)))
            case (None, Some(snd))      => Some(Pair(Proj(t, Fst), snd))
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd))

        // TODO: coercion for FunTy and PairTy

        case (VU(S0(vf)), VU(S1)) => Some(Lift(ctx.quote(vf), t))
        case (VLift(r1, a), VLift(r2, b)) =>
          unify(r1, r2)
          unify(a, b)
          None
        case (VLift(vf, a), b) => Some(coe(t.splice, a, S0(vf), b, st2))
        case (a, VLift(vf, b)) => Some(coe(t, a, st1, b, S0(vf)).quote)
        case _                 => justAdjust(t, a, st1, b, st2)
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
      case Some((_, vty, S1)) =>
        force(vty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def checkType(ty: S.Ty, s: Stage[VTy])(implicit ctx: Ctx): Tm =
    check(ty, VU(s), S1)

  private def check(tm: S.Tm, ty: Option[S.Ty], stage: Stage[VTy])(implicit
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

  private def check(tm: S.Tm, ty: VTy, stage: Stage[VTy])(implicit
      ctx: Ctx
  ): Tm =
    if !tm.isPos then
      debug(s"check $tm : ${ctx.pretty(ty)} : ${ctx.pretty(stage)}")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty, stage)(ctx.enter(pos))

      case (S.Lam(x, i, ot, b), VPi(y, i2, a, rt)) if icitMatch(i, y, i2) =>
        ot.foreach(t0 => {
          val ety = checkType(t0, S1)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, ctx.inst(rt), S1)(ctx.bind(x, a, S1))
        Lam(x, i2, eb)
      case (S.Lam(x, S.ArgIcit(Expl), ot, b), VFunTy(a, vf, rt)) =>
        unify(stage, S0(VVF()))
        ot.foreach(t0 => {
          val ety = checkType(t0, S0(VV()))
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, rt, S0(vf))
        Lam(x, Expl, eb)
      case (S.Var(x), VPi(_, Impl, _, _)) if hasMetaType(x) =>
        val Some((ix, varty, S1)) = ctx.lookup(x): @unchecked
        unify(varty, ty)
        Var(ix)
      case (tm, VPi(x, Impl, a, b)) =>
        val etm = check(tm, ctx.inst(b), S1)(ctx.bind(x, a, S1, true))
        Lam(x, Impl, etm)

      case (S.Pair(fst, snd), VSigma(_, a, b)) =>
        val efst = check(fst, a, S1)
        val esnd = check(snd, b(ctx.eval(efst)), S1)
        Pair(efst, esnd)
      case (S.Pair(fst, snd), VPairTy(a, b)) =>
        val efst = check(fst, a, S0(VV()))
        val esnd = check(snd, b, S0(VV()))
        Pair(efst, esnd)

      case (S.Lift(a), VU(S1)) =>
        val vf = newMeta(VVF(), S1)
        val ea = checkType(a, S0(ctx.eval(vf)))
        Lift(vf, ea)

      case (S.Pi(x, i, a, b), VU(S1)) =>
        val ea = checkType(a, S1)
        val va = ctx.eval(ea)
        val eb = checkType(b, S1)(ctx.bind(x, va, S1))
        Pi(x, i, ea, eb)
      case (S.Pi(x, Expl, a, b), VU(S0(vf))) =>
        unify(vf, VF())
        val ea = checkType(a, S0(VV()))
        val vf2 = newMeta(VVF(), S1)
        val vvf2 = ctx.eval(vf2)
        val eb = checkType(b, S0(vvf2))
        FunTy(ea, vf2, eb)
      case (S.Sigma(x, a, b), VU(S1)) =>
        val ea = checkType(a, S1)
        val va = ctx.eval(ea)
        val eb = checkType(b, S1)(ctx.bind(x, va, S1))
        Sigma(x, ea, eb)
      case (S.Sigma(x, a, b), VU(S0(vf))) =>
        unify(vf, VV())
        val ea = checkType(a, S0(VV()))
        val eb = checkType(b, S0(VV()))
        PairTy(ea, eb)

      case (S.Quote(t), VLift(vf, a)) => check(t, a, S0(vf)).quote
      case (t, VLift(vf, a))          => check(t, a, S0(vf)).quote

      case (S.Let(x, m, t, v, b), _) =>
        val vf = newMeta(VVF(), S1)
        val vvf = ctx.eval(vf)
        unify(if m then S1 else S0(vvf), stage)
        val vs = if m then S1 else S0(ctx.eval(newMeta(VVF(), S1)))
        val qvs = ctx.quote(vs)
        val (ev, et, vt) = check(v, t, vs)
        val eb = check(b, ty, stage)(
          ctx.define(x, vt, et, vs, qvs, ctx.eval(ev), ev)
        )
        Let(x, et, qvs, ev, eb)

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

  private def inferType(ty: S.Ty)(implicit ctx: Ctx): (Tm, Stage[VTy]) =
    val (t, a) = infer(ty, S1)
    force(a) match
      case VU(s) => (t, s)
      case ty    => error(s"expected type got ${ctx.pretty(ty)}")

  private def infer(tm: S.Tm, s: Stage[VTy])(implicit ctx: Ctx): (Tm, VTy) =
    if !tm.isPos then debug(s"infer $tm : ${ctx.pretty(s)}")
    tm match
      case S.Pos(pos, tm) => infer(tm, s)(ctx.enter(pos))

      case S.Lam(x, S.ArgIcit(i), ot, b) =>
        val (sa, sb) = s match
          case S1 => (S1, S1)
          case S0(vf) =>
            if i == Impl then error(s"implicit lambda cannot be in Ty: $tm")
            unify(vf, VF())
            val vf2 = ctx.eval(newMeta(VVF(), S1))
            (S0(VV()), S0(vf2))
        val a = ot match
          case None     => newMeta(VU(sa), S1)
          case Some(ty) => checkType(ty, sa)
        val va = ctx.eval(a)
        val (eb, rt) = infer(b, sb)(ctx.bind(x, va, sa))
        val fun = sb match
          case S1     => VPi(x, i, va, ctx.close(rt))
          case S0(vf) => VFunTy(va, vf, rt)
        (Lam(x, i, eb), fun)
      case S.Lam(x, S.ArgNamed(_), _, _) => error(s"cannot infer $tm")

      case S.Pair(fst, snd) =>
        s match
          case S1     =>
          case S0(vf) => unify(vf, VV())
        val (efst, fty) = infer(fst, s)
        val (esnd, sty) = infer(snd, s)
        val ty = s match
          case S1    => vsigma("_", fty, _ => sty)
          case S0(_) => VPairTy(fty, sty)
        (Pair(efst, esnd), ty)

      case S.Hole(ox) =>
        val ty = ctx.eval(newMeta(VU(s), S1))
        val t = newMeta(ty, s)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty, s))
        (t, ty)

      case _ =>
        val (t, a, si) = infer(tm)
        adjustStage(t, a, si, s)

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, Stage[VTy]) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))
      case S.U(S1)        => (U(S1), VU(S1), S1)
      case S.U(S0(vf)) =>
        val evf = check(vf, VVF(), S1)
        (U(S0(evf)), VU(S1), S1)
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
                  case Some(e) => (Global(x), e.vty, e.vstage)
                  case None    => error(s"undefined variable $x")
      case S.Let(x, m, t, v, b) =>
        val vs = if m then S1 else S0(ctx.eval(newMeta(VVF(), S1)))
        val qvs = ctx.quote(vs)
        val (ev, et, vt) = check(v, t, vs)
        val (eb, rt, st) =
          infer(b)(ctx.define(x, vt, et, vs, qvs, ctx.eval(ev), ev))
        (Let(x, et, qvs, ev, eb), rt, st)

      case S.Hole(ox) => error(s"cannot infer hole $tm")

      case S.Pi(x, Impl, a, b) =>
        val ea = checkType(a, S1)
        val eb = checkType(b, S1)(ctx.bind(x, ctx.eval(ea), S1))
        (Pi(x, Impl, ea, eb), VU(S1), S1)
      case S.Pi(x, _, a, b) =>
        val (ea, s) = inferType(a)
        s match
          case S1 =>
            val eb = checkType(b, S1)(ctx.bind(x, ctx.eval(ea), S1))
            (Pi(x, Expl, ea, eb), VU(S1), S1)
          case S0(vf) =>
            unify(vf, VV())
            val vfr = newMeta(VVF(), S1)
            val eb = checkType(b, S0(ctx.eval(vfr)))
            (FunTy(ea, vfr, eb), VU(S0(VF())), S1)

      case S.Sigma(x, a, b) =>
        val (ea, s) = inferType(a)
        s match
          case S1 =>
            val eb = checkType(b, S1)(ctx.bind(x, ctx.eval(ea), S1))
            (Sigma(x, ea, eb), VU(S1), S1)
          case S0(vf) =>
            unify(vf, VV())
            val eb = checkType(b, S0(VV()))
            (PairTy(ea, eb), VU(S0(VV())), S1)

      case S.Pair(fst, snd) =>
        val (efst, fstty, s1) = infer(fst)
        s1 match
          case S1 =>
            val (esnd, sndty) = infer(snd, S1)
            (
              Pair(efst, esnd),
              VSigma(DontBind, fstty, CFun(_ => sndty)),
              S1
            )
          case S0(vf) =>
            unify(vf, VV())
            val (esnd, sndty) = infer(snd, S0(VV()))
            (
              Pair(efst, esnd),
              VPairTy(fstty, sndty),
              S0(VV())
            )

      case S.Lam(x, S.ArgIcit(Impl), mty, b) =>
        val pty = mty match
          case Some(ty) =>
            val ety = checkType(ty, S1)
            ctx.eval(ety)
          case None =>
            val m = newMeta(VU(S1), S1)
            ctx.eval(m)
        val ctx2 = ctx.bind(x, pty, S1)
        val (eb, rty) = insert(S1, infer(b, S1)(ctx2))(ctx2)
        (Lam(x, Impl, eb), VPi(x, Impl, pty, ctx.close(rty)), S1)
      case S.Lam(x, S.ArgIcit(Expl), mty, b) =>
        val (pty, s) = mty match
          case Some(ty) =>
            val (ety, s) = inferType(ty)
            (ctx.eval(ety), s)
          case None => error(s"cannot infer unannotated lambda: $tm")
        s match
          case S1 =>
            val ctx2 = ctx.bind(x, pty, S1)
            val (eb, rty) = insert(S1, infer(b, S1)(ctx2))(ctx2)
            (Lam(x, Expl, eb), VPi(x, Expl, pty, ctx.close(rty)), S1)
          case S0(vf) =>
            unify(vf, VV())
            val ctx2 = ctx.bind(x, pty, s)
            val vf2 = ctx.eval(newMeta(VVF(), S1))
            val (eb, rty) = insert(S0(vf2), infer(b, S0(vf2))(ctx2))(ctx2)
            (Lam(x, Expl, eb), VFunTy(pty, vf2, rty), S0(VF()))
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
            val ea = check(a, pty, S1)
            (App(ef, ea, icit), rty(ctx.eval(ea)), S1)
          case VFunTy(pty, rvf, rty) =>
            if icit == Impl then error(s"implicit app in Ty: $tm")
            val ea = check(a, pty, S0(VV()))
            (App(ef, ea, icit), rty, S0(rvf))
          case _ =>
            st match
              case S1 =>
                val pty = ctx.eval(newMeta(VU(S1), S1))
                val x = DoBind(Name("x"))
                val rty =
                  CClos(ctx.env, newMeta(VU(S1), S1)(ctx.bind(x, pty, S1)))
                val ef2 = coe(ef, fty, S1, VPi(x, icit, pty, rty), S1)
                val ea = check(a, pty, S1)
                (App(ef2, ea, icit), rty(ctx.eval(ea)), S1)
              case S0(vf) =>
                if icit == Impl then error(s"implicit app in Ty: $tm")
                unify(vf, VF())
                val pty = ctx.eval(newMeta(VU(S0(VV())), S1))
                val rvf = ctx.eval(newMeta(VVF(), S1))
                val rty = ctx.eval(newMeta(VU(S0(rvf)), S1))
                val ef2 = coe(ef, fty, st, VFunTy(pty, rvf, rty), st)
                val ea = check(a, pty, S0(VV()))
                (App(ef2, ea, Expl), rty, S0(rvf))

      case S.Proj(t, p) =>
        val (et, ty, st) = insertPi(infer(t))
        (force(ty), p) match
          case (_, S.Named(x)) =>
            unify(st, S1)
            val (p, pty) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p), pty, S1)
          case (VSigma(_, fstty, _), S.Fst) => (Proj(et, Fst), fstty, S1)
          case (VSigma(_, _, sndty), S.Snd) =>
            (Proj(et, Snd), sndty(vfst(ctx.eval(et))), S1)
          case (VPairTy(fstty, _), S.Fst) => (Proj(et, Fst), fstty, S0(VV()))
          case (VPairTy(_, sndty), S.Snd) => (Proj(et, Snd), sndty, S0(VV()))
          case (tty, _) =>
            st match
              case S1 =>
                val pty = ctx.eval(newMeta(VU(S1), S1))
                val x = DoBind(Name("x"))
                val rty =
                  CClos(
                    ctx.env,
                    newMeta(VU(S1), S1)(ctx.bind(x, pty, S1))
                  )
                val et2 = coe(et, tty, S1, VSigma(x, pty, rty), S1)
                p match
                  case S.Fst => (Proj(et2, Fst), pty, S1)
                  case S.Snd => (Proj(et2, Snd), rty(vfst(ctx.eval(et2))), S1)
                  case _ => error(s"named projection with ambigious type: $tm")
              case S0(vf) =>
                unify(vf, VV())
                val pty = ctx.eval(newMeta(VU(S0(VV())), S1))
                val rty = ctx.eval(newMeta(VU(S0(VV())), S1))
                val et2 = coe(et, tty, S0(VV()), VPairTy(pty, rty), S0(VV()))
                p match
                  case S.Fst => (Proj(et2, Fst), pty, S0(VV()))
                  case S.Snd => (Proj(et2, Snd), rty, S0(VV()))
                  case _ => error(s"named projection with ambigious type: $tm")

      case S.Lift(a) =>
        val vf = newMeta(VVF(), S1)
        val ea = checkType(a, S0(ctx.eval(vf)))
        (Lift(vf, ea), VU(S1), S1)
      case S.Quote(t) =>
        val vf = ctx.eval(newMeta(VVF(), S1))
        val (et, a) = infer(t, S0(vf))
        (et.quote, VLift(vf, a), S1)
      case S.Splice(t) =>
        val (et, a) = infer(t, S1)
        val vf = ctx.eval(newMeta(VVF(), S1))
        val (et2, a2) = adjustStage(et, a, S1, S0(vf))
        (et2, a2, S0(vf))

  private def prettyHoles(implicit ctx0: Ctx): String =
    holes
      .map((x, e) =>
        e match
          case HoleEntry(ctx, tm, vty, s) =>
            s"_$x : ${ctx.pretty(vty)} : ${ctx.pretty(s)} = ${ctx
                .pretty(tm)}\nlocals:\n${ctx.prettyLocals}"
      )
      .mkString("\n\n")

  private def elaborate(tm: S.Tm, ty: Option[S.Ty], meta: Boolean)(implicit
      ctx: Ctx
  ): (Tm, Ty, Stage[Ty]) =
    resetMetas()
    holes.clear()

    val stage =
      if meta then S1
      else S0(ctx.eval(newMeta(VVF(), S1)))

    val (etm_, ety_, _) = check(tm, ty, stage)
    val etm = ctx.zonk(etm_)
    val ety = ctx.zonk(ety_)
    val estage = ctx.zonk(ctx.quote(stage))

    debug(
      s"elaborated ${ctx.pretty(etm)} : ${ctx.pretty(ety)} : ${ctx.pretty(stage)}"
    )
    if holes.nonEmpty then
      error(
        s"holes found: ${ctx.pretty(etm)} : ${ctx.pretty(ety)} : ${ctx
            .pretty(stage)}\n\n${prettyHoles}"
      )
    val ums = unsolvedMetas()
    if ums.nonEmpty then
      error(
        s"unsolved metas: ${ctx.pretty(etm)} : ${ctx
            .pretty(ety)}\n${ums
            .map((id, ty, s) => s"?$id : ${ctx.pretty(ty)} : ${ctx.pretty(s)}")
            .mkString("\n")}"
      )
    (etm, ety, estage)

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
            ctx.eval(ety),
            ctx.eval(estage)
          )
        )
        val ed = DDef(x, ety, estage, etm)
        debug(s"elaborated $ed")
        ed

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
