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
    try unify0(a, b)(ctx.lvl, ctx.unfoldSet)
    catch
      case err: UnifyError =>
        error(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  private def unify(a: Val, b: Val)(implicit ctx: Ctx): Unit =
    debug(s"unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
    try unify0(a, b)(ctx.lvl, ctx.unfoldSet)
    catch
      case err: UnifyError =>
        error(
          s"failed to unify ${ctx.pretty(a)} ~ ${ctx.pretty(b)}: ${err.msg}"
        )

  private def tryUnify(s1: VStage, s2: VStage, a: Val, b: Val)(implicit
      ctx: Ctx
  ): Boolean =
    debug(
      s"tryUnify ${ctx.pretty(a)} : ${ctx.pretty(s1)} ~ ${ctx.pretty(b)} : ${ctx.pretty(s2)}"
    )
    pushMetas()
    pushAutos()
    try
      unify0(s1, s2)(ctx.lvl, ctx.unfoldSet)
      unify0(a, b)(ctx.lvl, ctx.unfoldSet)
      useMetas()
      useAutos()
      true
    catch
      case err: UnifyError =>
        discardMetas()
        discardAutos()
        false

  // imports
  private val imports: mutable.Map[String, String] = mutable.Map.empty
  private val importedNames: mutable.Map[Name, (String, Name)] =
    mutable.Map.empty

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

  // auto search
  private var autos: mutable.ArrayBuffer[(Val, VTy, VStage, Ctx)] =
    mutable.ArrayBuffer.empty
  private val autoStack
      : mutable.ArrayBuffer[mutable.ArrayBuffer[(Val, VTy, VStage, Ctx)]] =
    mutable.ArrayBuffer.empty

  private def pushAutos(): Unit =
    autoStack += autos
    autos = autos.clone()

  private def useAutos(): Unit =
    autoStack.dropRightInPlace(1)

  private def discardAutos(): Unit =
    autos = autoStack.last
    autoStack.dropRightInPlace(1)

  private def tooBroad(ty: VTy): Boolean = force(ty) match
    case VFlex(id, spine) => true
    case VGlobal(_, _, sp, true, _) =>
      def args(sp: Spine): Option[List[Val]] = sp match
        case SId => Some(Nil)
        case SApp(spine, arg, icit) =>
          args(spine) match
            case None    => None
            case Some(l) => Some(arg :: l)
        case _ => None
      args(sp) match
        case None    => false
        case Some(l) => l.forall(tooBroad)
    case VLift(cv, v) => tooBroad(v)
    case _            => false

  private def searchAuto(m: Val, ty: VTy, st: VStage)(implicit
      ctx: Ctx
  ): Boolean =
    force(ty) match
      case ty if tooBroad(ty) => false
      case VUnitType()        => unify(m, VUnit()); true
      case VSigma(x, t1, t2c) =>
        val m1 = newMeta(t1, SMeta)
        val vm1 = ctx.eval(m1)
        val t2 = t2c(vm1)
        val m2 = newMeta(t2, SMeta)
        val vm2 = ctx.eval(m2)
        val res1 = searchAuto(vm1, t1, SMeta)
        val res2 = searchAuto(vm2, t2, SMeta)
        unify(m, VPair(vm1, vm2, ty))
        res1 && res2
      case _ =>
        allGlobals.foldLeft(false) {
          case (true, _)              => true
          case (_, (_, e)) if !e.auto => false
          case (_, ((mod, x), e)) =>
            val (etm, gty, gst) = insertPi((Global(mod, x), e.vty, e.vstage))
            if !tryUnify(gst, st, gty, ty) then false
            else
              val vetm = ctx.eval(etm)
              unify(m, vetm)
              true
        }

  // metas
  private def newMeta(ty: VTy, s: VStage)(implicit ctx: Ctx): Tm =
    force(ty) match
      case VUnitType() => Prim(PUnit)
      case _ =>
        val (closed, cclosed) = ctx.closeVTy(ty)
        val m = freshMeta(closed, cclosed, s)
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
        case VPi(_, y, PiImpl(search), a, b) =>
          mode match
            case Until(x) if DoBind(x) == y => (tm, ty, st)
            case _ =>
              val m = newMeta(a, st)
              val mv = ctx.eval(m)
              if search && !searchAuto(mv, a, st) then
                autos += ((mv, a, st, ctx))
              go(App(tm, m, Impl), b(mv), st)
        case _ =>
          mode match
            case Until(x) => error(s"no implicit pi found with parameter $x")
            case _        => (tm, ty, st)
    go(inp._1, inp._2, inp._3)

  private def insert(inp: (Tm, VTy, VStage, Uses))(implicit
      ctx: Ctx
  ): (Tm, VTy, VStage, Uses) =
    inp._1 match
      case Lam(_, Impl, _, _) => inp
      case _ =>
        val (a, b, c) = insertPi((inp._1, inp._2, inp._3))
        (a, b, c, inp._4)

  private def insert(s: VStage, inp: (Tm, VTy, Uses))(implicit
      ctx: Ctx
  ): (Tm, VTy, Uses) =
    val res = insert((inp._1, inp._2, s, inp._3))
    (res._1, res._2, inp._3)

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
      (forceWithSet(a, ctx.unfoldSet), forceWithSet(b, ctx.unfoldSet)) match
        case (VPi(u1, x, i, p1, r1), VPi(u2, x2, i2, p2, r2)) =>
          if u1 != u2 then
            error(
              s"usage mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          if i != i2 then
            error(
              s"plicity mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          val ctx2 = ctx.bind(u1, x, p2, SMeta)
          go(Var(ix0), p2, SMeta, p1, SMeta)(ctx2) match
            case None =>
              val v = VVar(ctx.lvl)
              val body =
                go(App(Wk(t), Var(ix0), i.toIcit), r1(v), SMeta, r2(v), SMeta)(
                  ctx2
                )
              body.map(Lam(pick(x, x2), i.toIcit, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i.toIcit),
                r1(ctx2.eval(coev0)),
                SMeta,
                r2(VVar(ctx.lvl)),
                SMeta
              )(ctx2) match
                case None =>
                  Some(
                    Lam(
                      pick(x, x2),
                      i.toIcit,
                      ctx.quote(b),
                      App(Wk(t), coev0, i.toIcit)
                    )
                  )
                case Some(body) =>
                  Some(Lam(pick(x, x2), i.toIcit, ctx.quote(b), body))

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

        case (VFun(u1, p1, cv, r1), VFun(u2, p2, cv2, r2)) =>
          if u1 != u2 then
            error(
              s"usage mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          unify(cv, cv2)
          val x = DoBind(Name("x"))
          val ctx2 = ctx.bind(Many, x, p2, SVTy())
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

        case (VFun(u1, p1, cv, r1), VPi(u, x, i, p2, r2)) =>
          if u1 != u then
            error(
              s"usage mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          if i == Impl then
            error(s"coerce error ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          val ctx2 = ctx.bind(u, x, p2, SMeta)
          val y = DoBind(Name("x"))
          go(Var(ix0), p2, SMeta, p1, SVTy())(ctx2) match
            case None =>
              val body =
                go(
                  App(Wk(t), Var(ix0), i.toIcit),
                  r1,
                  STy(cv),
                  r2(VVar(ctx.lvl)),
                  SMeta
                )(
                  ctx2
                )
              body.map(Lam(pick(y, x), i.toIcit, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i.toIcit),
                r1,
                STy(cv),
                r2(VVar(ctx.lvl)),
                SMeta
              )(ctx2) match
                case None =>
                  Some(
                    Lam(
                      pick(y, x),
                      i.toIcit,
                      ctx.quote(b),
                      App(Wk(t), coev0, i.toIcit)
                    )
                  )
                case Some(body) =>
                  Some(Lam(pick(y, x), i.toIcit, ctx.quote(b), body))
        case (VPi(u1, x, i, p1, r1), VFun(u, p2, cv, r2)) =>
          if u1 != u then
            error(
              s"usage mismatch ${ctx.pretty(t)} : ${ctx.pretty(a)} ~ ${ctx.pretty(b)}"
            )
          if i == Impl then
            error(s"coerce error ${ctx.pretty(a)} ~ ${ctx.pretty(b)}")
          val ctx2 = ctx.bind(Many, x, p2, SVTy())
          val y = DoBind(Name("x"))
          go(Var(ix0), p2, SVTy(), p1, SMeta)(ctx2) match
            case None =>
              val body =
                go(
                  App(Wk(t), Var(ix0), i.toIcit),
                  r1(VVar(ctx.lvl)),
                  SMeta,
                  r2,
                  STy(cv)
                )(
                  ctx2
                )
              body.map(Lam(pick(y, x), i.toIcit, ctx.quote(b), _))
            case Some(coev0) =>
              go(
                App(Wk(t), coev0, i.toIcit),
                r1(ctx2.eval(coev0)),
                SMeta,
                r2,
                STy(cv)
              )(ctx2) match
                case None =>
                  Some(
                    Lam(
                      pick(y, x),
                      i.toIcit,
                      ctx.quote(b),
                      App(Wk(t), coev0, i.toIcit)
                    )
                  )
                case Some(body) =>
                  Some(Lam(pick(y, x), i.toIcit, ctx.quote(b), body))

        case (VU(STy(cv)), VU(SMeta)) => Some(Lift(ctx.quote(cv), t))
        case (VFlex(_, _), _)         => justAdjust(t, a, st1, b, st2)
        case (_, VFlex(_, _))         => justAdjust(t, a, st1, b, st2)

        case (VLift(cv1, a), VLift(cv2, b)) =>
          unify(cv1, cv2); unify(a, b); None
        case (VLift(cv, a), b) => Some(coe(t.splice, a, STy(cv), b, st2))
        case (a, VLift(cv, b)) => Some(coe(t, a, st1, b, STy(cv)).quote)

        case (VConType(t1, c1), VConType(t2, c2)) =>
          unify(t1, t2); unify(c1, c2); None
        // Con A C <: A => $(exposeCon {at} {c} `t)
        case (VConType(at, c), et) =>
          unify(at, et);
          Some(
            App(
              App(
                App(Prim(PConExpose), ctx.quote(at), Impl),
                ctx.quote(c),
                Impl
              ),
              t.quote,
              Expl
            ).splice
          )

        case _ => justAdjust(t, a, st1, b, st2)
    go(t, a, st1, b, st2).getOrElse(t)

  // checking
  private def icitMatch(i1: S.ArgInfo, b: Bind, i2: PiIcit): Boolean = i1 match
    case S.ArgNamed(x) =>
      (b, i2) match
        case (DoBind(y), PiImpl(_)) => x == y
        case _                      => false
    case S.ArgIcit(i) => i.eqPiIcit(i2)

  private def hasMetaType(x: Name)(implicit ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some((_, _, vty, SMeta)) =>
        force(vty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def checkType(ty: S.Ty, s: VStage)(implicit ctx: Ctx): (Tm, Uses) =
    check(ty, VU(s), SMeta)(ctx.inType)
  private def checkVTy(ty: S.Ty)(implicit ctx: Ctx): (Tm, Uses) =
    check(ty, VVTy(), SMeta)(ctx.inType)

  private def check(
      tm: S.Tm,
      ty: Option[S.Ty],
      stage: VStage,
      topLevel: Boolean = false
  )(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy, Uses) = ty match
    case Some(ty0) =>
      val ty = ty0
      /*if !topLevel || !stage.isMeta then ty0
        else
          ty0.free.distinct
            .filter(x => getGlobal(x).isEmpty && !primNames.contains(x))
            .foldRight(ty0)((x, rt) => S.Pi(DoBind(x), Impl, S.Hole(None), rt))*/
      val (ety, u1) = checkType(ty, stage)
      val vty = ctx.eval(ety)
      val (etm, u2) = check(tm, vty, stage)
      (etm, ety, vty, u1 + u2)
    case None =>
      val (etm, vty, u) = infer(tm, stage)
      (etm, ctx.quote(vty), vty, u)

  private def check(tm: S.Tm, ty: VTy, stage: VStage)(implicit
      ctx: Ctx
  ): (Tm, Uses) =
    if !tm.isPos then
      debug(s"check $tm : ${ctx.pretty(ty)} : ${ctx.pretty(stage)}")
    (tm, forceWithSet(ty, ctx.unfoldSet)) match
      case (S.Pos(pos, tm), _) => check(tm, ty, stage)(ctx.enter(pos))

      case (S.Unfold(xs, b), _) => check(b, ty, stage)(ctx.unfold(xs))

      case (S.StringLit(v), VLift(cv, ty)) if stage.isMeta =>
        unify(cv, VVal())
        unify(ty, VForeignType(VStringLit("Ljava/lang/String;")))
        (StringLit(v).quote, ctx.uses)
      case (S.StringLit(v), _) =>
        val (etm, ty2, u) = insert(stage, infer(tm, stage))
        (coe(etm, ty2, stage, ty, stage), u)

      case (S.Lam(x, i, ot, b), VPi(u, y, i2, a, rt)) if icitMatch(i, y, i2) =>
        val us1 = ot
          .map(t0 => {
            val (ety, u) = checkType(t0, SMeta)
            unify(ctx.eval(ety), a)
            u
          })
          .getOrElse(ctx.uses)
        val (eb, us2) = check(b, ctx.inst(rt), SMeta)(ctx.bind(u, x, a, SMeta))
        val (uhd, utl) = us2.uncons
        if !(uhd <= u) then
          error(s"usage error for $x: expected ${u} but was ${uhd}")
        (Lam(x, i2.toIcit, ctx.quote(ty), eb), us1 + utl)
      case (S.Lam(x, S.ArgIcit(Expl), ot, b), VFun(u, a, cv, rt)) =>
        val u1 = ot
          .map(t0 => {
            val (ety, u1) = checkVTy(t0)
            unify(ctx.eval(ety), a)
            u1
          })
          .getOrElse(ctx.uses)
        val (eb, us) = check(b, rt, STy(cv))(ctx.bind(u, x, a, SVTy()))
        val (uhd, u2) = us.uncons
        if !(uhd <= u) then
          error(s"usage error for $x: expected ${u} but was ${uhd}")
        (Lam(x, Expl, ctx.quote(ty), eb), u1 + u2)
      case (S.Var(x, _), VPi(_, _, PiImpl(_), _, _)) if hasMetaType(x) =>
        val Some((_, ix, varty, SMeta)) = ctx.lookup(x): @unchecked
        unify(varty, ty)
        (Var(ix), ctx.use(ix))
      case (tm, VPi(u, x, PiImpl(_), a, b)) =>
        val (etm, us) =
          check(tm, ctx.inst(b), SMeta)(ctx.bind(u, x, a, SMeta, true))
        val (uhd, utl) = us.uncons
        if !(uhd <= u) then
          error(s"usage error for $x: expected ${u} but was ${uhd}")
        (Lam(x, Impl, ctx.quote(ty), etm), utl)

      case (S.Pair(fst, snd), VSigma(_, a, b)) =>
        val (efst, u1) = check(fst, a, SMeta)
        val (esnd, u2) = check(snd, b(ctx.eval(efst)), SMeta)
        (Pair(efst, esnd, ctx.quote(ty)), u1 + u2)

      case (S.Lift(a), VU(SMeta)) =>
        val cv = ctx.eval(newCV())
        val (eb, u) = checkType(a, STy(cv))
        (Lift(ctx.quote(cv), eb), u)

      case (S.Pi(u, x, i, a, b), VU(SMeta)) =>
        val (ea, u1) = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val (eb, us) = checkType(b, SMeta)(ctx.bind(Many, x, va, SMeta))
        val (_, u2) = us.uncons
        (Pi(u, x, i, ea, eb), u1 + u2)
      case (S.Pi(u, x, PiExpl, a, b), VUTy(cv)) =>
        unify(cv, VComp())
        val (ea, u1) = checkType(a, SVTy())
        val cv2 = newCV()
        val (eb, u2) = checkType(b, STy(ctx.eval(cv2)))
        (Fun(u, ea, cv2, eb), u1 + u2)
      case (S.Sigma(x, a, b), VU(SMeta)) =>
        val (ea, u1) = checkType(a, SMeta)
        val va = ctx.eval(ea)
        val (eb, us) = checkType(b, SMeta)(ctx.bind(Many, x, va, SMeta))
        val (_, u2) = us.uncons
        (Sigma(x, ea, eb), u1 + u2)

      case (S.Fix(g, x, b, arg), _) if !stage.isMeta =>
        val STy(cv) = stage: @unchecked
        val (earg, pty, uarg) = infer(arg, SVTy())
        val (eb, us) =
          check(b, ty, STy(cv))(
            ctx
              .bind(Many, g, VFun(Many, pty, cv, ty), SCTy())
              .bind(Many, x, pty, SVTy())
          )
        val (_, _, ub) = us.uncons2
        (Fix(ctx.quote(pty), ctx.quote(ty), g, x, eb, earg), uarg + ub)

      case (S.Match(scrut, cs, other), _) if !stage.isMeta =>
        val STy(vrcv) = stage: @unchecked
        checkMatch(scrut, cs, other, ctx.quote(ty), ty, vrcv)

      case (S.Con(c, None, as), VData(dx, cs, e)) if !stage.isMeta =>
        cs.find((c2, _) => c == c2) match
          case None =>
            error(
              s"constructor $c not found in expected type ${ctx.pretty(ty)}"
            )
          case Some((_, ts)) if as.size != ts.size =>
            error(
              s"invalid amount of arguments for constructor $c for expected type ${ctx
                  .pretty(ty)}: expected ${ts.size}, but got ${as.size}"
            )
          case Some((_, ts)) =>
            var u = ctx.uses
            val eas = as.zip(ts.map(_._2)).map { (a, t) =>
              val (ea, eu) = check(a, eval(t)(ty :: e), SVTy())
              u += eu
              ea
            }
            (Con(c, ctx.quote(ty), eas), u)

      case (S.Var(Name("[]"), _), VData(dx, cs, e)) if !stage.isMeta =>
        val nilary = cs.filter((_, as) => as.size == 0)
        if nilary.isEmpty then
          error(
            s"cannot check [] against ${ctx.pretty(ty)}: no nilary constructors"
          )
        if nilary.size > 1 then
          error(
            s"cannot check [] against ${ctx.pretty(ty)}: more than one nilary constructor"
          )
        val cx = nilary.head._1
        check(S.Con(cx, None, Nil), ty, stage)
      case (S.Pair(fst, snd), VData(dx, cs, e)) if !stage.isMeta =>
        val candidates = cs.filter((_, as) => as.size == 2)
        if candidates.isEmpty then
          error(
            s"cannot check pair against ${ctx.pretty(ty)}: no suitable constructors"
          )
        if candidates.size > 1 then
          error(
            s"cannot check pair against ${ctx.pretty(ty)}: more than one suitable constructor"
          )
        val cinfo = candidates.head
        val cx = cinfo._1
        val tfst = cinfo._2(0)._2
        val tsnd = cinfo._2(1)._2
        val (efst, u1) = check(fst, eval(tfst)(ty :: e), SVTy())
        val (esnd, u2) = check(snd, eval(tsnd)(ty :: e), SVTy())
        (Con(cx, ctx.quote(ty), List(efst, esnd)), u1 + u2)

      case (S.Quote(t), VLift(cv, a)) =>
        val (et, u) = check(t, a, STy(cv))
        (et.quote, u)
      case (t, VLift(cv, a)) =>
        val (et, u) = check(t, a, STy(cv))
        (et.quote, u)

      case (S.Let(u, x, m, t, v, b), _) if stage.isMeta == m =>
        val valstage = if m then SMeta else STy(newCV())
        val vvalstage = ctx.eval(valstage)
        val (ev, et, vt, uv) = check(v, t, vvalstage)
        val qstage = ctx.quote(stage)
        val (eb, us) = check(b, ty, stage)(
          ctx.define(Many, x, vt, et, vvalstage, valstage, ctx.eval(ev), ev)
        )
        val (ux, ub) = us.uncons
        if u != Many && !(ux <= u) then
          error(s"usage error for $x: expected ${u} but was ${ux}")
        (Let(u, x, et, valstage, ctx.quote(ty), ev, eb), (ux * uv) + ub)

      case (S.Hole(ox), _) =>
        val t = newMeta(ty, stage)
        ox.foreach(x => addHole(x, HoleEntry(ctx, t, ty, stage)))
        (t, ctx.uses)

      case (t, VFlex(_, _)) =>
        val (etm, vt, u) = insert(stage, infer(t, stage))
        (coe(etm, vt, stage, ty, stage), u)
      case _ =>
        val (etm, ty2, stage2, u) = insert(infer(tm))
        (coe(etm, ty2, stage2, ty, stage), u)

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
        Many,
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
      scrut: S.Tm,
      cs: List[(PosInfo, Name, Option[Name], List[Bind], S.Tm)],
      other: Option[(PosInfo, S.Tm)],
      rty: Tm,
      vrty: VTy,
      vrcv: VTy
  )(implicit ctx: Ctx): (Tm, Uses) =
    val (escrut, vscrutty, uscrut) = infer(scrut, SVTy())
    force(vscrutty) match
      case VConType(t, c) =>
        checkMatch(
          S.App(S.Var(Name("exposeCon")), scrut, S.ArgIcit(Expl)),
          cs,
          other,
          rty,
          vrty,
          vrcv
        )
      case VData(dx, dcs, e) =>
        val used = mutable.Set[Name]()
        val cons = dcs.map((cx, _) => cx).toSet
        val ecs = cs.map { (pos, cx, ocon, ps, b) =>
          implicit val ctx1: Ctx = ctx.enter(pos)
          if !cons.contains(cx) then
            error(s"$cx is not a constructor of type $dx")
          if used.contains(cx) then
            error(s"constructor appears twice in match $cx")
          used += cx
          val tas = dcs
            .find((cx2, as) => cx2 == cx)
            .get
            ._2
            .map(_._2)
            .map(t => eval(t)(vscrutty :: e))
          if ps.size != tas.size then
            error(
              s"datatype argument size mismatch, expected ${tas.size} but got ${ps.size}"
            )
          val (fnty0, ecv0) = tas
            .foldRight((vrty, vrcv)) { case (t, (rt, rcv)) =>
              (VFun(Many, t, rcv, rt), VComp())
            }
          val (fnty, ecv) = ocon.fold((fnty0, ecv0))(conx =>
            (
              VFun(
                Many,
                VConType(vscrutty, VStringLit(cx.expose)),
                ecv0,
                fnty0
              ),
              VComp()
            )
          )
          val lam0 =
            ps.foldRight(b)((p, b) => S.Lam(p, S.ArgIcit(Expl), None, b))
          val lam = ocon.fold(lam0)(conx =>
            S.Lam(DoBind(conx), S.ArgIcit(Expl), None, lam0)
          )
          val (eb, u) = check(lam, fnty, STy(ecv))
          (cx, ocon.isDefined, tas.size, eb, u)
        }
        val left = cons -- used
        if other.isEmpty && left.nonEmpty then
          error(
            s"non-exhaustive match, constructors left: ${left.mkString(" ")}"
          )
        val eother = other.map { (pos, b) =>
          implicit val ctxOther: Ctx = ctx.enter(pos)
          if left.isEmpty then error(s"other case does not match anything")
          check(b, vrty, STy(vrcv))
        }
        val uses = (eother, ecs.map(_._5)) match
          case (None, Nil)       => uscrut
          case (None, l)         => uscrut + Uses.lub(l)
          case (Some((_, u)), l) => uscrut + Uses.lub(u :: l)
        (
          Match(
            ctx.quote(vscrutty),
            rty,
            escrut,
            ecs.map((a, con, b, c, d) => (a, con, b, c)),
            eother.map(_._1)
          ),
          uses
        )
      case _ =>
        error(
          s"expected a datatype in match but got ${ctx.pretty(vscrutty)}"
        )

  private def inferType(ty: S.Ty)(implicit ctx: Ctx): (Tm, VStage, Uses) =
    val (t, a, u) = infer(ty, SMeta)
    force(a) match
      case VU(s) => (t, s, u)
      case ty    => error(s"expected type got ${ctx.pretty(ty)}")

  private def infer(tm: S.Tm, s: VStage)(implicit ctx: Ctx): (Tm, VTy, Uses) =
    if !tm.isPos then debug(s"infer $tm : ${ctx.pretty(s)}")
    tm match
      case S.Pos(pos, tm) => infer(tm, s)(ctx.enter(pos))

      case S.Unfold(xs, b) => infer(b, s)(ctx.unfold(xs))

      case S.StringLit(v) =>
        s match
          case SMeta =>
            (StringLit(v), VLabel(), ctx.uses)
          case STy(cv) =>
            unify(cv, VVal())
            (
              StringLit(v),
              VForeignType(VStringLit("Ljava/lang/String;")),
              ctx.uses
            )

      case S.Lam(x, S.ArgIcit(i), ot, b) =>
        s match
          case SMeta =>
            val (a, ut) = ot match
              case None     => (newMeta(VU(SMeta), SMeta), ctx.uses)
              case Some(ty) => checkType(ty, SMeta)
            val va = ctx.eval(a)
            val (eb, rt, u) = infer(b, SMeta)(ctx.bind(Many, x, va, SMeta))
            val (_, ub) = u.uncons
            (
              Lam(x, i, Irrelevant, eb),
              VPi(Many, x, i.toPiIcit, va, ctx.close(rt)),
              ut + ub
            )
          case STy(cvr) =>
            if i == Impl then error(s"implicit lambda cannot be in Ty: $tm")
            unify(cvr, VComp())
            val (a, ut) = ot match
              case None     => (newMeta(VVTy(), SMeta), ctx.uses)
              case Some(ty) => checkVTy(ty)
            val va = ctx.eval(a)
            val cv = ctx.eval(newCV())
            val rty0 = ctx.eval(newMeta(VUTy(cv), SMeta))
            val ctx2 = ctx.bind(Many, x, va, SVTy())
            val (eb0, ub) = check(b, rty0, STy(cv))(ctx2)
            val (eb, rty, ub2) = insert(STy(cv), (eb0, rty0, ub))(ctx2)
            val (u, ub3) = ub2.uncons
            val fty = VFun(Many, va, cv, rty)
            (Lam(x, Expl, ctx.quote(fty), eb), fty, ut + ub3)
      case S.Lam(x, S.ArgNamed(_), _, _) => error(s"cannot infer $tm")

      case S.Pair(fst, snd) =>
        s match
          case STy(_) => error(s"pair can only appear in meta stage: $tm")
          case SMeta =>
            val (efst, fty, u1) = infer(fst, SMeta)
            val (esnd, sty, u2) = infer(snd, SMeta)
            val ty = vsigma("_", fty, _ => sty)
            (Pair(efst, esnd, ctx.quote(ty)), ty, u1 + u2)

      case S.Hole(ox) =>
        val ty = ctx.eval(newMeta(VU(s), SMeta))
        val t = newMeta(ty, s)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty, s))
        (t, ty, ctx.uses)

      case S.Fix(g, x, b, arg) if !s.isMeta =>
        val STy(cv) = s: @unchecked
        val (earg, vty, uarg) = infer(arg, SVTy())
        val rty = newMeta(VUTy(cv), SMeta)
        val vrty = ctx.eval(rty)
        val ft = VFun(Many, vty, cv, vrty)
        val (eb, ub) =
          check(b, vrty, STy(cv))(
            ctx.bind(Many, g, ft, SCTy()).bind(Many, x, vty, SVTy())
          )
        val (_, _, ub2) = ub.uncons2
        (Fix(ctx.quote(vty), rty, g, x, eb, earg), vrty, uarg + ub2)

      case S.Match(scrut, cs, other) if !s.isMeta =>
        val STy(vrcv) = s: @unchecked
        val rty = newMeta(VUTy(vrcv), SMeta)
        val vrty = ctx.eval(rty)
        val (etm, u) = checkMatch(scrut, cs, other, rty, vrty, vrcv)
        (etm, vrty, u)

      case _ =>
        val (t, a, si, u) =
          if isRigidVar(tm) then infer(tm) else insert(infer(tm))
        debug(
          s"inferred $t : ${ctx.pretty(a)} : ${ctx.pretty(si)} to ${ctx.pretty(s)}"
        )
        val (et, ty) = adjustStage(t, a, si, s)
        (et, ty, u)

  private def isRigidVar(tm: S.Tm): Boolean = tm match
    case S.Var(x, true) => true
    case _              => false

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, VStage, Uses) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))
      case S.IntLit(v) =>
        (IntLit(v), VForeignType(VStringLit("I")), SVTy(), ctx.uses)
      case S.StringLit(v) => (StringLit(v), VLabel(), SMeta, ctx.uses)
      case S.Hole(ox)     => error(s"cannot infer hole $tm")
      case S.U(SMeta)     => (U(SMeta), VUMeta(), SMeta, ctx.uses)
      case S.U(STy(cv)) =>
        val (evf, u) = check(cv, VCV(), SMeta)
        (U(STy(evf)), VU(SMeta), SMeta, u)
      case S.Var(x, _) =>
        PrimName(x) match
          case Some(p) =>
            val (t, u) = primType(p)
            (Prim(p), t, u, ctx.uses)
          case None =>
            ctx.lookup(x) match
              case Some((vu, ix, ty, u)) => (Var(ix), ty, u, ctx.use(ix))
              case None =>
                val (module, y) =
                  val parts = x.expose.split("/", -1)
                  val y = Name(parts.last)
                  val m = parts.init.mkString("/")
                  if m.isEmpty then
                    if importedNames.contains(y) then importedNames(y)
                    else (ctx.module, y)
                  else (m, y)
                if !imports.contains(module) then
                  error(s"module $module is not imported")
                val realModule = imports(module)
                getGlobal(realModule, y) match
                  case Some(e) =>
                    (Global(realModule, y), e.vty, e.vstage, ctx.uses)
                  case None => error(s"undefined variable $x")

      case S.Let(u, x, m, t, v, b) =>
        val stage1 = if m then SMeta else STy(newCV())
        val vstage1 = ctx.eval(stage1)
        val stage2 = if m then SMeta else STy(newCV())
        val vstage2 = ctx.eval(stage2)
        val (ev, et, vt, uv) = check(v, t, vstage1)
        val (eb, rt, ub) =
          infer(b, vstage2)(
            ctx.define(Many, x, vt, et, vstage1, stage1, ctx.eval(ev), ev)
          )
        val (ux, ub2) = ub.uncons
        if u != Many && !(ux <= u) then
          error(s"usage error for $x: expected ${u} but was ${ux}")
        (
          Let(u, x, et, stage1, ctx.quote(rt), ev, eb),
          rt,
          vstage2,
          (ux * uv) + ub2
        )

      case S.Pi(u, x, i @ PiImpl(_), a, b) =>
        val (ea, u1) = checkType(a, SMeta)
        val (eb, us) =
          checkType(b, SMeta)(ctx.bind(Many, x, ctx.eval(ea), SMeta))
        val (_, u2) = us.uncons
        (Pi(u, x, i, ea, eb), VU(SMeta), SMeta, u1 + u2)
      case S.Pi(u, x, _, a, b) =>
        val (ea, s, u1) = inferType(a)
        s match
          case SMeta =>
            val (eb, us) =
              checkType(b, SMeta)(ctx.bind(Many, x, ctx.eval(ea), SMeta))
            val (_, u2) = us.uncons
            (Pi(u, x, PiExpl, ea, eb), VU(SMeta), SMeta, u1 + u2)
          case STy(rcv) =>
            unify(rcv, VVal())
            val cv = newCV()
            val (eb, u2) = checkType(b, STy(ctx.eval(cv)))
            (Fun(u, ea, cv, eb), VCTy(), SMeta, u1 + u2)

      case S.Sigma(x, a, b) =>
        val (ea, u1) = check(a, VUMeta(), SMeta)
        val (eb, us) =
          checkType(b, SMeta)(ctx.bind(Many, x, ctx.eval(ea), SMeta))
        val (_, u2) = us.uncons
        (Sigma(x, ea, eb), VU(SMeta), SMeta, u1 + u2)

      case S.Pair(fst, snd) =>
        val (efst, fstty, u1) = infer(fst, SMeta)
        val (esnd, sndty, u2) = infer(snd, SMeta)
        val ty = VSigma(DontBind, fstty, CFun(_ => sndty))
        (
          Pair(efst, esnd, ctx.quote(ty)),
          ty,
          SMeta,
          u1 + u2
        )

      case S.Lam(x, S.ArgIcit(Impl), mty, b) =>
        val (pty, ut) = mty match
          case Some(ty) =>
            val (ety, u) = checkType(ty, SMeta)
            (ctx.eval(ety), u)
          case None =>
            val m = newMeta(VU(SMeta), SMeta)
            (ctx.eval(m), ctx.uses)
        val ctx2 = ctx.bind(Many, x, pty, SMeta)
        val (eb, rty, ub) = insert(SMeta, infer(b, SMeta)(ctx2))(ctx2)
        val (_, ub2) = ub.uncons
        val fty = VPi(Many, x, PiImpl(false), pty, ctx.close(rty))
        (Lam(x, Impl, ctx.quote(fty), eb), fty, SMeta, ut + ub2)
      case S.Lam(x, S.ArgIcit(Expl), mty, b) =>
        val (pty, s, ut) = mty match
          case Some(ty) =>
            val (ety, s, u) = inferType(ty)
            (ctx.eval(ety), s, u)
          case None => error(s"cannot infer unannotated lambda: $tm")
        s match
          case SMeta =>
            val ctx2 = ctx.bind(Many, x, pty, SMeta)
            val (eb, rty, ub) = insert(SMeta, infer(b, SMeta)(ctx2))(ctx2)
            val (_, ub2) = ub.uncons
            val fty = VPi(Many, x, PiExpl, pty, ctx.close(rty))
            (Lam(x, Expl, ctx.quote(fty), eb), fty, SMeta, ut + ub2)
          case STy(rcv) =>
            unify(rcv, VVal())
            val ctx2 = ctx.bind(Many, x, pty, s)
            val cv = ctx.eval(newCV())
            val rty0 = ctx.eval(newMeta(VUTy(cv), SMeta))
            val (eb0, ub) = check(b, rty0, STy(cv))(ctx2)
            val (eb, rty, ub2) = insert(STy(cv), (eb0, rty0, ub))(ctx2)
            val (_, ub3) = ub2.uncons
            val fty = VFun(Many, pty, cv, rty)
            (Lam(x, Expl, ctx.quote(fty), eb), fty, STy(cv), ut + ub3)
      case S.Lam(_, S.ArgNamed(_), _, _) => error(s"cannot infer: $tm")

      case S.App(f, a, i) =>
        val (icit, ef, fty, st, uf) = i match
          case S.ArgNamed(x) =>
            val (a, b, c, u) = infer(f)
            val (ef, fty, st) = insertPi((a, b, c), Until(x))
            (Impl, ef, fty, st, u)
          case S.ArgIcit(Impl) =>
            val (ef, fty, st, u) = infer(f)
            (Impl, ef, fty, st, u)
          case S.ArgIcit(Expl) =>
            val (a, b, c, u) = infer(f)
            val (ef, fty, st) = insertPi((a, b, c))
            (Expl, ef, fty, st, u)
        force(fty) match
          case VPi(up, x, icit2, pty, rty) =>
            if !icit.eqPiIcit(icit2) then error(s"icit mismatch: $tm")
            val (ea, ua) = check(a, pty, SMeta)
            (App(ef, ea, icit), rty(ctx.eval(ea)), SMeta, uf + up * ua)
          case VFun(up, pty, rcv, rty) =>
            if icit == Impl then error(s"implicit app in Ty: $tm")
            val (ea, ua) = check(a, pty, SVTy())
            (App(ef, ea, icit), rty, STy(rcv), uf + up * ua)
          case _ =>
            st match
              case SMeta =>
                val pty = ctx.eval(newMeta(VU(SMeta), SMeta))
                val x = DoBind(Name("x"))
                val rty =
                  CClos(
                    ctx.env,
                    newMeta(VU(SMeta), SMeta)(ctx.bind(Many, x, pty, SMeta))
                  )
                val ef2 =
                  coe(
                    ef,
                    fty,
                    SMeta,
                    VPi(Many, x, icit.toPiIcit, pty, rty),
                    SMeta
                  )
                val (ea, ua) = check(a, pty, SMeta)
                (App(ef2, ea, icit), rty(ctx.eval(ea)), SMeta, uf + Many * ua)
              case STy(scv) =>
                if icit == Impl then error(s"implicit app in Ty: $tm")
                unify(scv, VComp())
                val pty = ctx.eval(newMeta(VVTy(), SMeta))
                val rcv = ctx.eval(newCV())
                val rty = ctx.eval(newMeta(VUTy(rcv), SMeta))
                val ef2 = coe(ef, fty, st, VFun(Many, pty, rcv, rty), st)
                val (ea, ua) = check(a, pty, SVTy())
                (App(ef2, ea, Expl), rty, STy(rcv), uf + Many * ua)

      case S.Proj(t, p) =>
        val (tmpa, tmpb, tmpc, ut) = infer(t)
        val (et, ty, st) = insertPi((tmpa, tmpb, tmpc))
        (force(ty), p) match
          case (VLift(_, inner), _) =>
            force(inner) match
              case VData(_, _, _) => infer(S.Proj(S.Splice(t), p))
              case _              => error(s"cannot project a lifted type")
          case (_, S.Named(x)) if st.isMeta =>
            val (p, pty) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p, Irrelevant, Irrelevant), pty, SMeta, ut)
          case (VSigma(_, fstty, _), S.Fst) =>
            (Proj(et, Fst, Irrelevant, Irrelevant), fstty, SMeta, ut)
          case (VSigma(_, _, sndty), S.Snd) =>
            val rt = sndty(vfst(ctx.eval(et)))
            (Proj(et, Snd, Irrelevant, Irrelevant), rt, SMeta, ut)
          case (VData(dx, cs, e), S.Named(px)) =>
            val candidates =
              cs.filter((_, as) => as.exists((y, _) => px == y.toName))
            if candidates.isEmpty then
              error(
                s"cannot project $px with type ${ctx.pretty(ty)}: no suitable constructors"
              )
            if candidates.size > 1 then
              error(
                s"cannot project $px with type ${ctx.pretty(ty)}: more than one suitable constructor"
              )
            val cinfo = candidates.head
            val cx = cinfo._1
            val cas = cinfo._2.map((x, t) => (x, eval(t)(ty :: e)))
            val x = Name("x")
            val i = cas.indexWhere((x, _) => px == x.toName)
            val pty = cas(i)._2
            val (em, ut) = check(
              S.Match(
                t,
                List(
                  (
                    ctx.pos,
                    cx,
                    None,
                    (0 until cas.size)
                      .map(j => if i == j then DoBind(x) else DontBind)
                      .toList,
                    S.Var(x)
                  )
                ),
                None
              ),
              pty,
              SVTy()
            )
            (em, pty, SVTy(), ut)
          case (VData(dx, cs, e), p) =>
            val candidates = cs.filter((_, as) => as.size == 2)
            if candidates.isEmpty then
              error(
                s"cannot project pair with type ${ctx.pretty(ty)}: no suitable constructors"
              )
            if candidates.size > 1 then
              error(
                s"cannot project pair with type ${ctx.pretty(ty)}: more than one suitable constructor"
              )
            val cinfo = candidates.head
            val cx = cinfo._1
            val cas = cinfo._2.map(_._2).map(t => eval(t)(ty :: e))
            val x = Name("x")
            p match
              case S.Fst =>
                val pty = cas(0)
                val (em, ut) = check(
                  S.Match(
                    t,
                    List(
                      (ctx.pos, cx, None, List(DoBind(x), DontBind), S.Var(x))
                    ),
                    None
                  ),
                  pty,
                  SVTy()
                )
                (em, pty, SVTy(), ut)
              case S.Snd =>
                val pty = cas(1)
                val (em, ut) = check(
                  S.Match(
                    t,
                    List(
                      (ctx.pos, cx, None, List(DontBind, DoBind(x)), S.Var(x))
                    ),
                    None
                  ),
                  pty,
                  SVTy()
                )
                (em, pty, SVTy(), ut)
              case S.Named(px) => impossible()
          case (tty, _) =>
            st match
              case SMeta =>
                val pty = ctx.eval(newMeta(VU(SMeta), SMeta))
                val x = DoBind(Name("x"))
                val rty =
                  CClos(
                    ctx.env,
                    newMeta(VU(SMeta), SMeta)(ctx.bind(Many, x, pty, SMeta))
                  )
                val et2 = coe(et, tty, SMeta, VSigma(x, pty, rty), SMeta)
                p match
                  case S.Fst =>
                    (Proj(et2, Fst, Irrelevant, Irrelevant), pty, SMeta, ut)
                  case S.Snd =>
                    val ty = rty(vfst(ctx.eval(et2)))
                    (Proj(et2, Snd, Irrelevant, Irrelevant), ty, SMeta, ut)
                  case _ => error(s"named projection with ambigious type: $tm")
              case STy(_) => error(s"projection in Ty: $tm")

      case S.Fix(g, x, b, arg) =>
        val (earg, vty, uarg) = infer(arg, SVTy())
        val cv = ctx.eval(newCV())
        val rty = newMeta(VUTy(cv), SMeta)
        val vrty = ctx.eval(rty)
        val ft = VFun(Many, vty, cv, vrty)
        val (eb, ub1) =
          check(b, vrty, STy(cv))(
            ctx.bind(Many, g, ft, SCTy()).bind(Many, x, vty, SVTy())
          )
        val (_, _, ub) = ub1.uncons2
        (Fix(ctx.quote(vty), rty, g, x, eb, earg), vrty, STy(cv), uarg + ub)

      case S.Match(scrut, cs, other) =>
        val vrcv = ctx.eval(newCV())
        val rty = newMeta(VUTy(vrcv), SMeta)
        val vrty = ctx.eval(rty)
        val (etm, u) = checkMatch(scrut, cs, other, rty, vrty, vrcv)
        (etm, vrty, STy(vrcv), u)

      case S.Lift(a) =>
        val cv = newCV()
        val vcv = ctx.eval(cv)
        val (ea, u) = checkType(a, STy(vcv))
        (Lift(cv, ea), VU(SMeta), SMeta, u)
      case S.Quote(t) =>
        val cv = ctx.eval(newCV())
        val (et, a, u) = infer(t, STy(cv))
        (et.quote, VLift(cv, a), SMeta, u)
      case S.Splice(t) =>
        val (et, a, u) = infer(t, SMeta)
        val cv = ctx.eval(newCV())
        val (et2, a2) = adjustStage(et, a, SMeta, STy(cv))
        (et2, a2, STy(cv), u)

      case S.Data(x, cs) =>
        val cons = cs.map((_, cx, _) => cx)
        val newctx = ctx.bind(Many, x, VVTy(), SMeta)
        var u = ctx.uses
        val ecs = cs.map((pos, c, as) =>
          (
            c,
            as.map { (x, a) =>
              val (ea, eu) = check(a, VVTy(), SMeta)(newctx.enter(pos))
              u += eu.tail
              (x, ea)
            }
          )
        )
        (Data(x, ecs), VVTy(), SMeta, u)

      case S.Con(c, None, as) => error("cannot infer con without expected type")
      case tmc @ S.Con(c, Some(t), as) =>
        val (et, u) = checkVTy(t)
        val vt = ctx.eval(et)
        val (ec, u2) = check(tmc, vt, SVTy())
        (ec, vt, SVTy(), u + u2)

      case S.Foreign(io, rt, l, as) =>
        val (ert, u1) = checkVTy(rt)
        val (el, u2) = check(l, VLabel(), SMeta)
        val eas1 =
          as.map(a => infer(a, SVTy())).map((a, t, u) => (a, ctx.quote(t), u))
        val eas = eas1.map((a, b, c) => (a, b))
        val us = eas1.map(_._3).foldLeft(u1 + u2)(_ + _)
        if io then (Foreign(io, ert, el, eas), VIO(ctx.eval(ert)), SCTy(), us)
        else (Foreign(io, ert, el, eas), ctx.eval(ert), SVTy(), us)

      case S.Unfold(xs, b) =>
        infer(b)(ctx.unfold(xs))

  // elaboration
  private def solveAutos(): Unit =
    debug(s"solveAutos ${autos.size}")
    val newautos = autos
      .clone()
      .map { case e @ (m, ty, st, ctx) =>
        if searchAuto(m, ty, st)(ctx) then None else Some(e)
      }
      .flatten
    if newautos.nonEmpty then
      autos = newautos
      solveAutos()

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
    val (etm_, ety_, _, _) = check(tm, ty, vstage, true)

    if autos.nonEmpty then solveAutos()

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
    val (etm1, ety1) =
      if ums.nonEmpty && !estage.isMeta then
        error(
          s"unsolved metas: ${ctx.pretty(etm)} : ${ctx
              .pretty(ety)}\n${ums
              .map((id, ty, s) => s"?$id : ${ctx.pretty(ty)} : $s")
              .mkString("\n")}"
        )
      else if estage.isMeta then
        val uu = orderUnsolvedMetas
        val tt =
          orderUnsolvedMetas.map(id => (id, ctx.zonk(getMetaUnsolved(id).cty)))
        tt.foldRight((etm, ety)) { case ((id, mty), (tm, ty)) =>
          val x = DoBind(Name(mty match
            case Prim(PCV) => "cv"
            case U(SMeta)  => "M"
            case U(STy(_)) => "T"
            case _         => s"x$id"
          ))
          val nty = Pi(Many, x, PiImpl(false), mty, replaceMeta(id, ty, ix0))
          val ntm = Lam(x, Impl, nty, replaceMeta(id, tm, ix0))
          (ntm, nty)
        }
      else (etm, ety)
    (etm1, ety1, estage)

  private def replaceMeta(id: MetaId, t: Tm, ix: Ix): Tm = t match
    case Var(ix)      => t
    case Irrelevant   => t
    case Global(_, _) => t
    case Prim(name)   => t
    case IntLit(_)    => t
    case StringLit(_) => t

    case Meta(id1) if id == id1 => Var(ix)
    case Meta(id)               => t

    case U(stage)     => U(stage.map(replaceMeta(id, _, ix)))
    case Lift(cv, tm) => Lift(replaceMeta(id, cv, ix), replaceMeta(id, tm, ix))
    case Quote(tm)    => Quote(replaceMeta(id, tm, ix))
    case Splice(tm)   => Splice(replaceMeta(id, tm, ix))
    case Wk(tm)       => Wk(replaceMeta(id, tm, ix))
    case Data(x, cs) =>
      Data(
        x,
        cs.map((c, as) => (c, as.map((x, t) => (x, replaceMeta(id, t, ix)))))
      )
    case Con(x, t, as) =>
      Con(
        x,
        replaceMeta(id, t, ix),
        as.map(replaceMeta(id, _, ix))
      )
    case Pair(fst, snd, ty) =>
      Pair(
        replaceMeta(id, fst, ix),
        replaceMeta(id, snd, ix),
        replaceMeta(id, ty, ix)
      )
    case Proj(tm, proj, ty, pty) =>
      Pair(
        replaceMeta(id, tm, ix),
        replaceMeta(id, ty, ix),
        replaceMeta(id, pty, ix)
      )
    case AppPruning(tm, spine) => AppPruning(replaceMeta(id, tm, ix), spine)

    case Let(u, name, ty, stage, bty, value, body) =>
      Let(
        u,
        name,
        replaceMeta(id, ty, ix),
        stage.map(replaceMeta(id, _, ix)),
        replaceMeta(id, bty, ix),
        replaceMeta(id, value, ix),
        replaceMeta(id, body, ix + 1)
      )
    case Pi(u, name, icit, ty, body) =>
      Pi(u, name, icit, replaceMeta(id, ty, ix), replaceMeta(id, body, ix + 1))
    case Fun(u, a, b, c) =>
      Fun(
        u,
        replaceMeta(id, a, ix),
        replaceMeta(id, b, ix),
        replaceMeta(id, c, ix)
      )
    case Lam(name, icit, fnty, body) =>
      Lam(name, icit, replaceMeta(id, fnty, ix), replaceMeta(id, body, ix + 1))
    case App(fn, arg, icit) =>
      App(replaceMeta(id, fn, ix), replaceMeta(id, arg, ix), icit)
    case Fix(ty, rty, g, x, b, arg) =>
      Fix(
        replaceMeta(id, ty, ix),
        replaceMeta(id, rty, ix),
        g,
        x,
        replaceMeta(id, b, ix + 2),
        replaceMeta(id, arg, ix)
      )
    case Sigma(name, ty, body) =>
      Sigma(name, replaceMeta(id, ty, ix), replaceMeta(id, body, ix + 1))
    case Match(dty, rty, scrut, cs, other) =>
      Match(
        replaceMeta(id, dty, ix),
        replaceMeta(id, rty, ix),
        replaceMeta(id, scrut, ix),
        cs.map((x, c, i, t) => (x, c, i, replaceMeta(id, t, ix))),
        other.map(replaceMeta(id, _, ix))
      )

    case Foreign(io, rt, cmd, args) =>
      Foreign(
        io,
        replaceMeta(id, rt, ix),
        replaceMeta(id, cmd, ix),
        args.map((a, b) => (replaceMeta(id, a, ix), replaceMeta(id, b, ix)))
      )

  private def elaborate(module: String, d: S.Def): List[Def] =
    debug(s"elaborate $module $d")
    d match
      case S.DImport(pos, m, mx, xs_, hiding) =>
        imports += (mx.map(_.expose).getOrElse(m) -> m)
        xs_ match
          case None if hiding.isEmpty => Nil
          case _ =>
            val toHide = hiding.getOrElse(Nil)
            val xsPre = xs_ match
              case None            => allNamesFromModule(m).map(x => (x, x))
              case Some(Left(_))   => allNamesFromModule(m).map(x => (x, x))
              case Some(Right(xs)) => xs.map((o, x) => (o.getOrElse(x), x))
            val hideLeft = toHide.filterNot(x => xsPre.exists((_, y) => x == y))
            if hideLeft.size > 0 then
              error(s"hiding invalid name: ${hideLeft.mkString(", ")}")(
                Ctx.empty(pos, module)
              )
            val xs = xsPre.filterNot((_, x) => toHide.contains(x))
            xs.foreach { (x, y) =>
              if getGlobal(module, x).isDefined || importedNames.contains(x)
              then
                error(s"cannot import $x from $m, it is already defined")(
                  Ctx.empty(pos, module)
                )
              importedNames += (x -> (m, y))
            }
            Nil
      case S.DDef(pos, auto, opq, x, m, t, v) =>
        implicit val ctx: Ctx = Ctx.empty(pos, module)
        if getGlobal(module, x).isDefined || importedNames.contains(x) then
          error(s"duplicate global $x")
        val (etm, ety, estage) = elaborate(v, t, m)
        setGlobal(
          GlobalEntry(
            auto,
            opq,
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
      case S.DData(pos, dx, ps, cs) =>
        implicit val ctx: Ctx = Ctx.empty(pos, module)

        if getGlobal(module, dx).isDefined || importedNames.contains(dx) then
          error(s"duplicate datatype $dx")
        val vty = U(STy(Prim(PVal)))
        val svty = S.U(STy(S.Var(Name("Val"))))
        val tconTm = ps.foldRight(S.Data(DoBind(dx), cs))((p, b) =>
          S.Lam(DoBind(p), S.ArgIcit(Expl), Some(svty), b)
        )
        val (tcon, tconvty, _, _) = infer(tconTm)
        val tconty = ctx.quote(tconvty)
        setGlobal(
          GlobalEntry(
            false,
            false,
            module,
            dx,
            tcon,
            tconty,
            SMeta,
            ctx.eval(tcon),
            tconvty,
            SMeta
          )
        )

        // check cases
        val ccs = {
          val ccs = cs.map { (pos, cx, as) =>
            if getGlobal(module, cx).isDefined || importedNames.contains(cx)
            then error(s"duplicate datatype constructor $cx")
            val conTy = ps.foldRight(
              S.Let(
                Many,
                dx,
                true,
                None,
                ps.foldLeft(S.Var(dx))((f, x) =>
                  S.App(f, S.Var(x), S.ArgIcit(Expl))
                ),
                as.foldRight(S.Var(dx)) { case ((x, t), b) =>
                  S.Pi(Many, x, PiExpl, t, b)
                }
              )
            )((p, b) => S.Pi(Many, DoBind(p), PiImpl(false), svty, b))
            val conTm = as.zipWithIndex.foldRight(
              S.Con(
                cx,
                None,
                as.zipWithIndex.map { case ((x, _), i) =>
                  val y = x match
                    case DoBind(x) => x
                    case DontBind  => Name(s"a$i")
                  S.Var(y)
                }
              )
            ) { case (((x, t), i), b) =>
              val y = x match
                case DoBind(x) => x
                case DontBind  => Name(s"a$i")
              S.Lam(DoBind(y), S.ArgIcit(Expl), None, b)
            }

            val (econTy, _) = check(conTy, VUMeta(), SMeta)
            val vconTy = ctx.eval(econTy)
            val (econTm, _) = check(conTm, vconTy, SMeta)
            val neconTy = ctx.quote(vconTy)

            setGlobal(
              GlobalEntry(
                false,
                false,
                module,
                cx,
                econTm,
                neconTy,
                SMeta,
                ctx.eval(econTm),
                vconTy,
                SMeta
              )
            )

            List(DDef(module, cx, neconTy, SMeta, econTm))
          }

          ccs
        }

        List(DDef(module, dx, tconty, SMeta, tcon)) ++ ccs.flatten

  def elaborate(module: String, uri: String, ds: S.Defs): Defs =
    debug(s"elaborate $module $uri")
    imports.clear()
    imports += (module -> module)
    importedNames.clear()
    try Defs(ds.toList.flatMap(d => elaborate(module, d)))
    catch case e: ElaborateError => throw ElaborateError(e.pos, uri, e.msg)
