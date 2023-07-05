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

  // metas
  private def newMeta(ty: VTy, s: VStage)(implicit ctx: Ctx): Tm =
    force(ty) match
      case VUnitType() => Prim(PUnit)
      case _ =>
        val closed = ctx.closeVTy(ty)
        val m = freshMeta(closed, s)
        debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
        AppPruning(Meta(m), ctx.pruning)

  private def newCV()(implicit ctx: Ctx): Tm = newMeta(VCV(), SMeta)

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
      case (STy(cv1), STy(cv2)) => unify(cv1, cv2); None
      case (STy(cv), SMeta)     => Some((t.quote, VLift(cv, a)))
      case (SMeta, STy(cv)) =>
        debug(s"$t : ${ctx.pretty(a)} : ${ctx.pretty(s1)} to ${ctx.pretty(s2)}")
        val m = ctx.eval(newMeta(VUTy(cv), SMeta))
        unify(a, VLift(cv, m))
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
    def pick(x: Bind, y: Bind)(implicit ctx: Ctx): Bind = (x, y) match
      case (DontBind, DontBind) => DoBind(Name("x"))
      case (DontBind, x)        => x
      case (x, DontBind)        => x
      case (_, x)               => x
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

        case (VFun(p1, cv, r1), VFun(p2, cv2, r2)) =>
          unify(cv, cv2)
          val x = DoBind(Name("x"))
          val ctx2 = ctx.bind(x, p2, SVTy())
          go(Var(ix0), p2, SVTy(), p1, SVTy())(ctx2) match
            case None =>
              val body =
                go(App(Wk(t), Var(ix0), Expl), r1, STy(cv), r2, STy(cv))(ctx2)
              body.map(Lam(x, Expl, ctx.quote(b), _))
            case Some(coev0) =>
              go(App(Wk(t), coev0, Expl), r1, STy(cv), r2, STy(cv))(ctx2) match
                case None =>
                  Some(Lam(x, Expl, ctx.quote(b), App(Wk(t), coev0, Expl)))
                case Some(body) => Some(Lam(x, Expl, ctx.quote(b), body))

        case (VFun(p1, cv, r1), VPi(x, i, p2, r2)) =>
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
                  STy(cv),
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
                STy(cv),
                r2(VVar(ctx.lvl)),
                SMeta
              )(ctx2) match
                case None =>
                  Some(Lam(pick(y, x), i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(pick(y, x), i, ctx.quote(b), body))
        case (VPi(x, i, p1, r1), VFun(p2, cv, r2)) =>
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
                  STy(cv)
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
                STy(cv)
              )(ctx2) match
                case None =>
                  Some(Lam(pick(y, x), i, ctx.quote(b), App(Wk(t), coev0, i)))
                case Some(body) => Some(Lam(pick(y, x), i, ctx.quote(b), body))

        case (VU(STy(cv)), VU(SMeta)) => Some(Lift(ctx.quote(cv), t))
        case (VFlex(_, _), _)         => justAdjust(t, a, st1, b, st2)
        case (_, VFlex(_, _))         => justAdjust(t, a, st1, b, st2)
        case (VLift(cv1, a), VLift(cv2, b)) =>
          unify(cv1, cv2); unify(a, b); None
        case (VLift(cv, a), b) => Some(coe(t.splice, a, STy(cv), b, st2))
        case (a, VLift(cv, b)) => Some(coe(t, a, st1, b, STy(cv)).quote)
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
      case (S.Lam(x, S.ArgIcit(Expl), ot, b), VFun(a, cv, rt)) =>
        ot.foreach(t0 => {
          val ety = checkVTy(t0)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, rt, STy(cv))(ctx.bind(x, a, SVTy()))
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

      case (S.Lift(a), VU(SMeta)) =>
        val cv = ctx.eval(newCV())
        Lift(ctx.quote(cv), checkType(a, STy(cv)))

      case (S.Pi(x, i, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Pi(x, i, ea, eb)
      case (S.Pi(x, Expl, a, b), VUTy(cv)) =>
        unify(cv, VComp())
        val ea = checkType(a, SVTy())
        val cv2 = newCV()
        val eb = checkType(b, STy(ctx.eval(cv2)))
        Fun(ea, cv2, eb)
      case (S.Sigma(x, a, b), VU(SMeta)) =>
        val ea = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val eb = checkType(b, SMeta)(ctx.bind(x, va, SMeta))
        Sigma(x, ea, eb)

      case (S.Fix(g, x, b, arg), _) if !stage.isMeta =>
        val STy(cv) = stage: @unchecked
        val (earg, pty) = infer(arg, SVTy())
        val eb =
          check(b, ty, STy(cv))(
            ctx.bind(g, VFun(pty, cv, ty), SCTy()).bind(x, pty, SVTy())
          )
        Fix(ctx.quote(pty), ctx.quote(ty), g, x, eb, earg)

      case (S.Match(scrut, cs, other), _) if !stage.isMeta =>
        val STy(vrcv) = stage: @unchecked
        val etm = checkMatch(tm, scrut, cs, other, ctx.quote(ty), ty, vrcv)
        etm

      case (S.Var(Name("[]")), VTCon(dx, as)) if !stage.isMeta =>
        val nilary = getGlobalData(dx).get._2.filter((_, as) => as.isEmpty)
        if nilary.isEmpty then
          error(
            s"cannot check [] against ${ctx.pretty(ty)}: no nilary constructors"
          )
        if nilary.size > 1 then
          error(
            s"cannot check [] against ${ctx.pretty(ty)}: more than one nilary constructor: ${nilary.keySet
                .mkString(" ")}"
          )
        val cx = nilary.head._1
        check(S.Var(cx), ty, stage)
      case (S.Pair(fst, snd), VTCon(dx, as)) if !stage.isMeta =>
        val datainfo = getGlobalData(dx).get
        val candidates = datainfo._2.filter((_, as) => as.size == 2)
        if candidates.isEmpty then
          error(
            s"cannot check pair against ${ctx.pretty(ty)}: no suitable constructors"
          )
        if candidates.size > 1 then
          error(
            s"cannot check pair against ${ctx.pretty(ty)}: more than one suitable constructor: ${candidates.keySet
                .mkString(" ")}"
          )
        val cinfo = candidates.head
        val cx = cinfo._1
        val cas = cinfo._2
        val ctxConsTypes = datatypeCtx(datainfo._1, as)
        val efst = check(fst, ctxConsTypes.eval(cas(0)), SVTy())
        val esnd = check(snd, ctxConsTypes.eval(cas(1)), SVTy())
        Con(dx, cx, as.map(ctx.quote(_)), List(efst, esnd))

      case (S.Quote(t), VLift(cv, a)) => check(t, a, STy(cv)).quote
      case (t, VLift(cv, a))          => check(t, a, STy(cv)).quote

      case (S.Let(x, m, t, v, b), _) if stage.isMeta == m =>
        val valstage = if m then SMeta else STy(newCV())
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

  private def datatypeCtx(ps: List[Name], as: List[Val])(implicit
      ctx: Ctx
  ): Ctx =
    ps.zipWithIndex.foldLeft(ctx) { case (ctx, (x, i)) =>
      ctx.define(
        x,
        VVTy(),
        ctx.quote(VVTy()),
        SMeta,
        SMeta,
        as(i),
        ctx.quote(as(i))
      )
    }
  private def checkMatch(
      tm: S.Tm,
      scrut: S.Tm,
      cs: List[(PosInfo, Name, List[Bind], S.Tm)],
      other: Option[(PosInfo, S.Tm)],
      rty: Tm,
      vrty: VTy,
      vrcv: VTy
  )(implicit ctx: Ctx): Tm =
    val (escrut, vscrutty) = infer(scrut, SVTy())
    force(vscrutty) match
      case VFlex(_, _) =>
        // try to figure out datatype from constructors
        val used = cs.flatMap(c => getGlobalCon(c._2).map(_._1))
        if used.isEmpty then error(s"match contains undefined constructors")
        val name = used.head
        val arity = getGlobalData(name).get._1.size
        val data = (0 until arity).toList
          .map(_ => newMeta(VVTy(), SMeta))
          .foldLeft(Global(name))((f, a) => App(f, a, Expl))
        unify(vscrutty, ctx.eval(data))
        checkMatch(tm, scrut, cs, other, rty, vrty, vrcv)
      case VTCon(dx, as) =>
        val (dps, cons) = getGlobalData(dx).get
        val ctxConsTypes = datatypeCtx(dps, as)
        val used = mutable.Set[Name]()
        val ecs = cs.map { (pos, cx, ps, b) =>
          implicit val ctx1: Ctx = ctx.enter(pos)
          if !cons.contains(cx) then
            error(s"$cx is not a constructor of type $dx: $tm")
          if used.contains(cx) then
            error(s"constructor appears twice in match $cx: $tm")
          used += cx
          val tas = cons(cx)
          if ps.size != tas.size then
            error(
              s"datatype argument size mismatch, expected ${tas.size} but got ${ps.size}"
            )
          val (fnty, ecv) = tas
            .foldRight((vrty, vrcv)) { case (t, (rt, rcv)) =>
              (VFun(ctxConsTypes.eval(t), rcv, rt), VComp())
            }
          val lam =
            ps.foldRight(b)((p, b) => S.Lam(p, S.ArgIcit(Expl), None, b))
          val eb = check(lam, fnty, STy(ecv))
          (cx, tas.size, eb)
        }
        val left = cons.keySet -- used
        if other.isEmpty && left.nonEmpty then
          error(
            s"non-exhaustive match, constructors left: ${left.mkString(" ")}"
          )
        val eother = other.map { (pos, b) =>
          implicit val ctxOther: Ctx = ctx.enter(pos)
          if left.isEmpty then error(s"other case does not match anything")
          check(b, vrty, STy(vrcv))
        }
        Match(ctx.quote(vscrutty), rty, escrut, ecs, eother)
      case _ =>
        error(
          s"expected a datatype in match but got ${ctx.pretty(vscrutty)} in $tm"
        )

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
          case STy(cvr) =>
            if i == Impl then error(s"implicit lambda cannot be in Ty: $tm")
            unify(cvr, VComp())
            val a = ot match
              case None     => newMeta(VVTy(), SMeta)
              case Some(ty) => checkVTy(ty)
            val va = ctx.eval(a)
            val cv = ctx.eval(newCV())
            val rty0 = ctx.eval(newMeta(VUTy(cv), SMeta))
            val ctx2 = ctx.bind(x, va, SVTy())
            val eb0 = check(b, rty0, STy(cv))(ctx2)
            val (eb, rty) = insert(STy(cv), (eb0, rty0))(ctx2)
            val fty = VFun(va, cv, rty)
            (Lam(x, Expl, ctx.quote(fty), eb), fty)
      case S.Lam(x, S.ArgNamed(_), _, _) => error(s"cannot infer $tm")

      case S.Pair(fst, snd) =>
        s match
          case STy(_) => error(s"pair can only appear in meta stage: $tm")
          case SMeta =>
            val (efst, fty) = infer(fst, SMeta)
            val (esnd, sty) = infer(snd, SMeta)
            val ty = vsigma("_", fty, _ => sty)
            (Pair(efst, esnd, ctx.quote(ty)), ty)

      case S.Hole(ox) =>
        val ty = ctx.eval(newMeta(VU(s), SMeta))
        val t = newMeta(ty, s)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty, s))
        (t, ty)

      case S.Fix(g, x, b, arg) if !s.isMeta =>
        val STy(cv) = s: @unchecked
        val (earg, vty) = infer(arg, SVTy())
        val rty = newMeta(VUTy(cv), SMeta)
        val vrty = ctx.eval(rty)
        val ft = VFun(vty, cv, vrty)
        val eb =
          check(b, vrty, STy(cv))(ctx.bind(g, ft, SCTy()).bind(x, vty, SVTy()))
        (Fix(ctx.quote(vty), rty, g, x, eb, earg), vrty)

      case S.Match(scrut, cs, other) if !s.isMeta =>
        val STy(vrcv) = s: @unchecked
        val rty = newMeta(VUTy(vrcv), SMeta)
        val vrty = ctx.eval(rty)
        val etm = checkMatch(tm, scrut, cs, other, rty, vrty, vrcv)
        (etm, vrty)

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
      case S.U(SMeta)     => (U(SMeta), VUMeta(), SMeta)
      case S.U(STy(cv)) =>
        val evf = check(cv, VCV(), SMeta)
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
        val stage1 = if m then SMeta else STy(newCV())
        val vstage1 = ctx.eval(stage1)
        val stage2 = if m then SMeta else STy(newCV())
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
          case STy(rcv) =>
            unify(rcv, VVal())
            val cv = newCV()
            val eb = checkType(b, STy(ctx.eval(cv)))
            (Fun(ea, cv, eb), VCTy(), SMeta)

      case S.Sigma(x, a, b) =>
        val ea = check(a, VUMeta(), SMeta)
        val eb = checkType(b, SMeta)(ctx.bind(x, ctx.eval(ea), SMeta))
        (Sigma(x, ea, eb), VU(SMeta), SMeta)

      case S.Pair(fst, snd) =>
        val (efst, fstty) = infer(fst, SMeta)
        val (esnd, sndty) = infer(snd, SMeta)
        val ty = VSigma(DontBind, fstty, CFun(_ => sndty))
        (
          Pair(efst, esnd, ctx.quote(ty)),
          ty,
          SMeta
        )

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
          case STy(rcv) =>
            unify(rcv, VVal())
            val ctx2 = ctx.bind(x, pty, s)
            val cv = ctx.eval(newCV())
            val rty0 = ctx.eval(newMeta(VUTy(cv), SMeta))
            val eb0 = check(b, rty0, STy(cv))(ctx2)
            val (eb, rty) = insert(STy(cv), (eb0, rty0))(ctx2)
            val fty = VFun(pty, cv, rty)
            (Lam(x, Expl, ctx.quote(fty), eb), fty, STy(cv))
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
          case VFun(pty, rcv, rty) =>
            if icit == Impl then error(s"implicit app in Ty: $tm")
            val ea = check(a, pty, SVTy())
            (App(ef, ea, icit), rty, STy(rcv))
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
              case STy(scv) =>
                if icit == Impl then error(s"implicit app in Ty: $tm")
                unify(scv, VComp())
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rcv = ctx.eval(newCV())
                val rty = ctx.eval(newMeta(VUTy(rcv), SMeta))
                val ef2 = coe(ef, fty, st, VFun(pty, rcv, rty), st)
                val ea = check(a, pty, SVTy())
                (App(ef2, ea, Expl), rty, STy(rcv))

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
          case (VLift(_, inner), _) =>
            force(inner) match
              case VTCon(_, _) => infer(S.Proj(S.Splice(t), p))
              case _           => error(s"cannot project a lifted type")
          case (VTCon(dx, as), p) =>
            val datainfo = getGlobalData(dx).get
            val candidates = datainfo._2.filter((_, as) => as.size == 2)
            if candidates.isEmpty then
              error(
                s"cannot project pair with type ${ctx.pretty(ty)}: no suitable constructors"
              )
            if candidates.size > 1 then
              error(
                s"cannot project pair with type ${ctx.pretty(ty)}: more than one suitable constructor: ${candidates.keySet
                    .mkString(" ")}"
              )
            val cinfo = candidates.head
            val cx = cinfo._1
            val cas = cinfo._2
            val datactx = datatypeCtx(datainfo._1, as)
            val x = Name("x")
            p match
              case S.Fst =>
                val pty = datactx.eval(cas(0))
                val em = check(
                  S.Match(
                    t,
                    List((ctx.pos, cx, List(DoBind(x), DontBind), S.Var(x))),
                    None
                  ),
                  pty,
                  SVTy()
                )
                (em, pty, SVTy())
              case S.Snd =>
                val pty = datactx.eval(cas(1))
                val em = check(
                  S.Match(
                    t,
                    List((ctx.pos, cx, List(DontBind, DoBind(x)), S.Var(x))),
                    None
                  ),
                  pty,
                  SVTy()
                )
                (em, pty, SVTy())
              case _ => impossible()
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
              case STy(_) => error(s"projection in Ty: $tm")

      case S.Fix(g, x, b, arg) =>
        val (earg, vty) = infer(arg, SVTy())
        val cv = ctx.eval(newCV())
        val rty = newMeta(VUTy(cv), SMeta)
        val vrty = ctx.eval(rty)
        val ft = VFun(vty, cv, vrty)
        val eb =
          check(b, vrty, STy(cv))(ctx.bind(g, ft, SCTy()).bind(x, vty, SVTy()))
        (Fix(ctx.quote(vty), rty, g, x, eb, earg), vrty, STy(cv))

      case S.Match(scrut, cs, other) =>
        val vrcv = ctx.eval(newCV())
        val rty = newMeta(VUTy(vrcv), SMeta)
        val vrty = ctx.eval(rty)
        val etm = checkMatch(tm, scrut, cs, other, rty, vrty, vrcv)
        (etm, vrty, STy(vrcv))

      case S.Lift(a) =>
        val cv = newCV()
        val vcv = ctx.eval(cv)
        val ea = checkType(a, STy(vcv))
        (Lift(cv, ea), VU(SMeta), SMeta)
      case S.Quote(t) =>
        val cv = ctx.eval(newCV())
        val (et, a) = infer(t, STy(cv))
        (et.quote, VLift(cv, a), SMeta)
      case S.Splice(t) =>
        val (et, a) = infer(t, SMeta)
        val cv = ctx.eval(newCV())
        val (et2, a2) = adjustStage(et, a, SMeta, STy(cv))
        (et2, a2, STy(cv))

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

    val vstage = if meta then SMeta else STy(ctx.eval(newCV()))
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
      case S.DDef(pos, x, m, t, v) =>
        implicit val ctx: Ctx = Ctx.empty(pos)
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
      case S.DData(pos, dx, ps, cs) =>
        implicit val ctx: Ctx = Ctx.empty(pos)
        if getGlobalData(dx).isDefined then error(s"duplicate datatype $dx")

        // generate tcon
        if getGlobal(dx).isDefined then error(s"duplicate datatype $dx")
        val vty = U(STy(Prim(PVal)))
        val tconty = ps.foldRight(vty)((_, t) => Pi(DontBind, Expl, vty, t))
        val tcon =
          ps.foldRight[(Tm, Ty)](
            (
              TCon(dx, (0 until ps.size).reverse.map(i => Var(mkIx(i))).toList),
              vty
            )
          ) { case (x, (b, t)) =>
            val ty = Pi(DontBind, Expl, vty, t)
            (Lam(DoBind(x), Expl, ty, b), ty)
          }._1
        setGlobal(
          GlobalEntry(
            dx,
            tcon,
            tconty,
            SMeta,
            ctx.eval(tcon),
            ctx.eval(tconty),
            SMeta
          )
        )

        // check cases
        val ccs = {
          implicit val casectx1: Ctx =
            ps.foldLeft(ctx)((ctx, x) => ctx.bind(DoBind(x), VVTy(), SMeta))
          val ccs = cs.map { (pos, cx, as) =>
            implicit val casectx2: Ctx = casectx1.enter(pos)
            if getGlobal(cx).isDefined then
              error(s"duplicate datatype constructor $cx")
            val cas = as.map { ta =>
              // TODO: check recursion
              val cta = check(ta, VVTy(), SMeta)
              cta
            }

            // add global for datatype case
            val rty = Lift(
              Prim(PVal),
              (0 until ps.size).reverse.foldLeft(Global(dx))((f, i) =>
                App(f, Var(mkIx(i)), Expl)
              )
            )
            val targs =
              (0 until ps.size).reverse
                .map(i => Var(mkIx(i + cas.size)))
                .toList
            val args =
              (0 until cas.size).reverse.map(i => Splice(Var(mkIx(i)))).toList
            val body = Quote(Con(dx, cx, targs, args))
            val (con, conty) =
              ps.foldRight[(Tm, Ty)](
                cas.zipWithIndex.foldRight[(Tm, Ty)]((body, rty)) {
                  case ((ty, i), (b, rt)) =>
                    val nty = Pi(DontBind, Expl, Lift(Prim(PVal), ty), Wk(rt))
                    (Lam(DoBind(Name(s"a$i")), Expl, nty, b), nty)
                }
              ) { case (p, (b, rt)) =>
                val nty = Pi(DoBind(p), Impl, vty, rt)
                (Lam(DoBind(p), Impl, nty, b), nty)
              }

            setGlobal(
              GlobalEntry(
                cx,
                con,
                conty,
                SMeta,
                ctx.eval(con),
                ctx.eval(conty),
                SMeta
              )
            )

            ((cx, cas), DDef(cx, conty, SMeta, con))
          }
          ccs
        }

        setGlobalData(dx, ps, ccs.map(_._1))

        List(DData(dx, ps, ccs.map(_._1)), DDef(dx, tconty, SMeta, tcon)) ++ ccs
          .map(_._2)

  def elaborate(uri: String, ds: S.Defs): Defs =
    try Defs(ds.toList.flatMap(d => elaborate(d)))
    catch case e: ElaborateError => throw ElaborateError(e.pos, uri, e.msg)
