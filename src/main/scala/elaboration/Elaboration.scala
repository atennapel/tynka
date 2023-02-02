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

  // metas
  private def newMeta(ty: VTy, s: VStage)(implicit ctx: Ctx): Tm =
    force(ty) match
      case VUnitType() => Prim(PUnit)
      case _ =>
        val closed = ctx.closeVTy(ty)
        val m = freshMeta(closed, s)
        debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
        AppPruning(Meta(m), ctx.pruning)

  private def newVF()(implicit ctx: Ctx): Tm = newMeta(VVF(), SMeta)

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

        case (VSigma(x, p1, r1), VSigma(x2, p2, r2)) =>
          val fst =
            go(Proj(t, Fst, Irrelevant, Irrelevant), p1, SMeta, p2, SMeta)
          val f = vfst(ctx.eval(t))
          val snd = fst match
            case None =>
              go(
                Proj(t, Snd, Irrelevant, Irrelevant),
                r1(f),
                SMeta,
                r2(f),
                SMeta
              )
            case Some(fst) =>
              go(
                Proj(t, Snd, Irrelevant, Irrelevant),
                r1(f),
                SMeta,
                r2(ctx.eval(fst)),
                SMeta
              )
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(
                Pair(fst, Proj(t, Snd, Irrelevant, Irrelevant), ctx.quote(b))
              )
            case (None, Some(snd)) =>
              Some(
                Pair(Proj(t, Fst, Irrelevant, Irrelevant), snd, ctx.quote(b))
              )
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))

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

        case (VTPair(p1, r1), VTPair(p2, r2)) =>
          val fst =
            go(
              Proj(t, Fst, ctx.quote(p1), ctx.quote(a)),
              p1,
              SVTy(),
              p2,
              SVTy()
            )
          val snd =
            go(
              Proj(t, Snd, ctx.quote(r1), ctx.quote(a)),
              r1,
              SVTy(),
              r2,
              SVTy()
            )
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(
                Pair(
                  fst,
                  Proj(t, Snd, ctx.quote(r1), ctx.quote(a)),
                  ctx.quote(b)
                )
              )
            case (None, Some(snd)) =>
              Some(
                Pair(
                  Proj(t, Fst, ctx.quote(p1), ctx.quote(a)),
                  snd,
                  ctx.quote(b)
                )
              )
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))

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

        case (VTPair(p1, r1), VSigma(_, p2, r2)) =>
          val fst =
            go(Proj(t, Fst, ctx.quote(p1), ctx.quote(a)), p1, SVTy(), p2, SMeta)
          val snd = fst match
            case None =>
              go(
                Proj(t, Snd, ctx.quote(r1), ctx.quote(a)),
                r1,
                SVTy(),
                r2(vfst(ctx.eval(t))),
                SMeta
              )
            case Some(fst) =>
              go(
                Proj(t, Snd, ctx.quote(r1), ctx.quote(a)),
                r1,
                SVTy(),
                r2(ctx.eval(fst)),
                SMeta
              )
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(
                Pair(
                  fst,
                  Proj(t, Snd, ctx.quote(r1), ctx.quote(a)),
                  ctx.quote(b)
                )
              )
            case (None, Some(snd)) =>
              Some(
                Pair(
                  Proj(t, Fst, ctx.quote(p1), ctx.quote(a)),
                  snd,
                  ctx.quote(b)
                )
              )
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))
        case (VSigma(_, p1, r1), VTPair(p2, r2)) =>
          val fst =
            go(Proj(t, Fst, Irrelevant, Irrelevant), p1, SMeta, p2, SVTy())
          val f = vfst(ctx.eval(t))
          val snd = fst match
            case None =>
              go(Proj(t, Snd, Irrelevant, Irrelevant), r1(f), SMeta, r2, SVTy())
            case Some(fst) =>
              go(Proj(t, Snd, Irrelevant, Irrelevant), r1(f), SMeta, r2, SVTy())
          (fst, snd) match
            case (None, None) => None
            case (Some(fst), None) =>
              Some(
                Pair(fst, Proj(t, Snd, Irrelevant, Irrelevant), ctx.quote(b))
              )
            case (None, Some(snd)) =>
              Some(
                Pair(Proj(t, Fst, Irrelevant, Irrelevant), snd, ctx.quote(b))
              )
            case (Some(fst), Some(snd)) => Some(Pair(fst, snd, ctx.quote(b)))

        case (VU(STy(vf)), VU(SMeta)) => Some(Lift(ctx.quote(vf), t))
        case (VLift(vf1, a), VLift(vf2, b)) =>
          unify(vf1, vf2); unify(a, b); None
        case (VFlex(_, _), _)  => justAdjust(t, a, st1, b, st2)
        case (_, VFlex(_, _))  => justAdjust(t, a, st1, b, st2)
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

      case (S.Pair(fst, snd), VSigma(_, a, b)) =>
        val efst = check(fst, a, SMeta)
        val esnd = check(snd, b(ctx.eval(efst)), SMeta)
        Pair(efst, esnd, ctx.quote(ty))
      case (S.Pair(fst, snd), VTPair(a, b)) =>
        val efst = check(fst, a, SVTy())
        val esnd = check(snd, b, SVTy())
        Pair(efst, esnd, ctx.quote(ty))

      case (S.Lift(a), VU(SMeta)) =>
        val vf = ctx.eval(newVF())
        Lift(ctx.quote(vf), checkType(a, STy(vf)))

      case (S.Pi(x, i, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Pi(x, i, ea, eb)
      case (S.Pi(x, Expl, a, b), VUTy(vf)) =>
        unify(vf, VFun())
        val ea = checkType(a, SVTy())
        val vf2 = newVF()
        val eb = checkType(b, STy(ctx.eval(vf2)))
        tfun(ea, vf2, eb)
      case (S.Sigma(x, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Sigma(x, ea, eb)
      case (S.Sigma(x, a, b), VUTy(vf)) =>
        unify(vf, VVal())
        val ea = checkVTy(a)
        val eb = checkVTy(b)
        tpair(ea, eb)

      case (S.Con(i, as), VTCon(_, b)) =>
        val cs = b(ty)
        if i < 0 || i >= cs.size || as.size != cs(i).size then
          error(s"invalid constructor $tm : ${ctx.pretty(ty)}")
        val eas = as.zip(cs(i)).map((a, vt) => check(a, vt, SVTy()))
        Con(ctx.quote(ty), i, eas)

      case (S.Case(s, cs), _) if !stage.isMeta =>
        val STy(vf) = stage: @unchecked
        val (es, sty) = infer(s, SVTy())
        val vcs = force(sty) match
          case VTCon(_, b) => b(sty)
          case _ if cs eq Nil =>
            unify(sty, VTCon(DontBind, TConClos(Nil, Nil))); Nil
          case _ =>
            error(
              s"ambigious datatype in $tm: ${ctx.pretty(sty)}"
            )
        if cs.size != vcs.size then
          error(s"invalid number of cases, expected ${vcs.size}: $tm")
        val ecs = cs.zip(vcs).map { (c, ts) =>
          val (cty, rvf) = ts.foldRight((ty, vf)) { case (pt, (rt, vf)) =>
            (VTFun(pt, vf, rt), VFun())
          }
          check(c, cty, STy(rvf))
        }
        Case(ctx.quote(sty), ctx.quote(ty), es, ecs)

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
            unify(vfr, VFun())
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

      case S.Pair(fst, snd) =>
        val (efst, fty) = infer(fst, s)
        val (esnd, sty) = infer(snd, s)
        val ty = s match
          case SMeta => vsigma("_", fty, _ => sty)
          case STy(vf) =>
            unify(vf, VVal())
            VTPair(fty, sty)
        (Pair(efst, esnd, ctx.quote(ty)), ty)

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
      case S.IntLit(n)    => (IntLit(n), VInt(), SVTy())
      case S.U(SMeta)     => (U(SMeta), VUMeta(), SMeta)
      case S.U(STy(vf)) =>
        val evf = check(vf, VVF(), SMeta)
        (U(STy(evf)), VU(SMeta), SMeta)
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
            unify(rvf, VVal())
            val vf = newVF()
            val eb = checkType(b, STy(ctx.eval(vf)))
            (tfun(ea, vf, eb), VFTy(), SMeta)

      case S.Sigma(x, a, b) =>
        val (ea, s) = inferType(a)
        s match
          case SMeta =>
            val eb = checkType(b, SMeta)(ctx.bind(x, ctx.eval(ea), SMeta))
            (Sigma(x, ea, eb), VU(SMeta), SMeta)
          case STy(rvf) =>
            unify(rvf, VVal())
            val eb = checkVTy(b)
            (tpair(ea, eb), VVTy(), SMeta)

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
          case STy(rvf) =>
            unify(rvf, VVal())
            val (esnd, vta) = infer(snd, SVTy())
            val ty = VTPair(fstty, vta)
            (Pair(efst, esnd, ctx.quote(ty)), ty, SVTy())

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
            unify(rvf, VVal())
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
                unify(svf, VFun())
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rvf = ctx.eval(newVF())
                val rty = ctx.eval(newMeta(VUTy(rvf), SMeta))
                val ef2 = coe(ef, fty, st, VTFun(pty, rvf, rty), st)
                val ea = check(a, pty, SVTy())
                (App(ef2, ea, Expl), rty, STy(rvf))

      case S.Proj(t, p) =>
        val (et, ty, st) = insertPi(infer(t))
        (force(ty), p) match
          case (_, S.Named(x)) =>
            if st != SMeta then error(s"can only do named projection in Meta")
            val (p, pty) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p, Irrelevant, Irrelevant), pty, SMeta)
          case (VSigma(_, fstty, _), S.Fst) =>
            (Proj(et, Fst, Irrelevant, Irrelevant), fstty, SMeta)
          case (VSigma(_, _, sndty), S.Snd) =>
            val rt = sndty(vfst(ctx.eval(et)))
            (Proj(et, Snd, Irrelevant, Irrelevant), rt, SMeta)
          case (VTPair(fstty, _), S.Fst) =>
            (Proj(et, Fst, ctx.quote(fstty), ctx.quote(ty)), fstty, SVTy())
          case (VTPair(_, sndty), S.Snd) =>
            (Proj(et, Snd, ctx.quote(sndty), ctx.quote(ty)), sndty, SVTy())
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
                  case S.Fst =>
                    (Proj(et2, Fst, Irrelevant, Irrelevant), pty, SMeta)
                  case S.Snd =>
                    val ty = rty(vfst(ctx.eval(et2)))
                    (Proj(et2, Snd, Irrelevant, Irrelevant), ty, SMeta)
                  case _ => error(s"named projection with ambigious type: $tm")
              case STy(rvf) =>
                unify(rvf, VVal())
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rty = ctx.eval(newMeta(VVTy(), SMeta))
                val et2 = coe(et, tty, SVTy(), VTPair(pty, rty), SVTy())
                p match
                  case S.Fst =>
                    (Proj(et2, Fst, ctx.quote(pty), ctx.quote(ty)), pty, SVTy())
                  case S.Snd =>
                    (Proj(et2, Snd, ctx.quote(rty), ctx.quote(ty)), rty, SVTy())
                  case _ => error(s"named projection in Ty: $tm")

      case S.TCon(x, cs) =>
        val ctx2 = ctx.bind(x, VVTy(), SMeta)
        val ecs = cs.map(as => as.map(t => check(t, VVTy(), SMeta)(ctx2)))
        (TCon(x, ecs), VVTy(), SMeta)
      case S.Con(_, _) => error(s"cannot infer: $tm")

      case S.Case(scrut, cs) =>
        val vf = ctx.eval(newVF())
        val m = newMeta(VUTy(vf), SMeta)
        val vm = ctx.eval(m)
        val etm = check(tm, vm, STy(vf))
        (etm, vm, STy(vf))

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

  private def elaborate(d: S.Def): List[Def] =
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
        List(ed)
      case S.DData(x, ps, cs) =>
        val vty = S.U(STy(S.Var(Name("Val"))))
        val tcond = S.DDef(
          x,
          true,
          Some(ps.foldRight(vty)((x, rt) => S.Pi(DoBind(x), Expl, vty, rt))),
          ps.foldRight(S.TCon(DoBind(x), cs.map(_._2)))((x, b) =>
            S.Lam(DoBind(x), S.ArgIcit(Expl), None, b)
          )
        )
        val ed = elaborate(tcond)
        val ecs = cs.zipWithIndex.flatMap { case ((c, ts), i) =>
          val rt =
            ps.foldLeft(S.Var(x))((f, x) => S.App(f, S.Var(x), S.ArgIcit(Expl)))
          def replace(t: S.Ty): S.Ty = t match
            case S.Pos(p, t)        => S.Pos(p, replace(t))
            case S.Var(z) if z == x => rt
            case _                  => t
          val tsty =
            ts.foldRight(rt)((t, b) => S.Pi(DontBind, Expl, replace(t), b))
          val ty = ps.foldRight(tsty)((x, b) => S.Pi(DoBind(x), Impl, vty, b))
          val ns = ts.zipWithIndex.map((_, i) => Name(s"a$i"))
          val body = ns.foldRight(S.Con(i, ns.map(S.Var.apply)))((x, b) =>
            S.Lam(DoBind(x), S.ArgIcit(Expl), None, b)
          )
          val cond = S.DDef(c, true, Some(ty), body)
          elaborate(cond)
        }
        ed ++ ecs

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.flatMap(elaborate))
