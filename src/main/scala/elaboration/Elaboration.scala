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
import core.Ctx

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
  private final case class HoleEntry(ctx: Ctx, tm: Tm, ty: VTy, univ: VUniv)
  private val holes: mutable.Map[Name, HoleEntry] = mutable.Map.empty

  // metas
  private def newMeta(ty: VTy)(implicit ctx: Ctx): Tm = force(ty) match
    case VUnitType() => Prim(PUnit)
    case _ =>
      val closed = ctx.closeVTy(ty)
      val m = freshMeta(closed)
      debug(s"newMeta ?$m : ${ctx.pretty(ty)}")
      AppPruning(Meta(m), ctx.pruning)

  private enum InsertMode:
    case All
    case Until(name: Name)
  import InsertMode.*

  private def insertPi(inp: (Tm, VTy), mode: InsertMode = All)(implicit
      ctx: Ctx
  ): (Tm, VTy) =
    @tailrec
    def go(tm: Tm, ty: VTy): (Tm, VTy) = force(ty) match
      case VPi(y, Impl, a, b) =>
        mode match
          case Until(x) if x == y => (tm, ty)
          case _ =>
            val m = newMeta(a)
            val mv = ctx.eval(m)
            go(App(tm, m, Impl), b(mv))
      case _ =>
        mode match
          case Until(x) => error(s"no implicit pi found with parameter $x")
          case _        => (tm, ty)
    go(inp._1, inp._2)

  private def insert(inp: (Tm, VTy))(implicit ctx: Ctx): (Tm, VTy) =
    inp._1 match
      case Lam(_, Impl, _) => inp
      case _               => insertPi(inp)

  // elaboration
  private def icitMatch(i1: S.ArgInfo, b: Bind, i2: Icit): Boolean = i1 match
    case S.ArgNamed(x) =>
      (b, i2) match
        case (DoBind(y), Impl) => x == y
        case _                 => false
    case S.ArgIcit(i) => i == i2

  private def hasMetaType(x: Name)(implicit ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some((_, vty, _)) =>
        force(vty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def piUniv(a: VUniv, b: VUniv)(implicit ctx: Ctx): VUniv =
    (force(a), force(b)) match
      case (VMetaTy(), _) => unify(a, b); a
      case (_, VMetaTy()) => unify(a, b); b
      case (VTy(_), _) =>
        unify(a, VTyV())
        val vf = ctx.eval(newMeta(VVF()))
        unify(b, VTy(vf))
        VTyF()
      case (_, VTy(_)) =>
        unify(a, VTyV())
        val vf = ctx.eval(newMeta(VVF()))
        unify(b, VTy(vf))
        VTyF()
      case _ =>
        error(
          s"ambigious pi universe: ${ctx.pretty(a)} and ${ctx.pretty(b)}"
        )

  private def sigmaUniv(a: VUniv, b: VUniv)(implicit ctx: Ctx): VUniv =
    (force(a), force(b)) match
      case (VMetaTy(), _) => unify(a, b); a
      case (_, VMetaTy()) => unify(a, b); b
      case (VTy(_), _)    => unify(a, VTyV()); unify(b, VTyV()); a
      case (_, VTy(_))    => unify(a, VTyV()); unify(b, VTyV()); b
      case _ =>
        error(
          s"ambigious sigma universe: ${ctx.pretty(a)} and ${ctx.pretty(b)}"
        )

  private def checkType(tm: S.Ty)(implicit ctx: Ctx): (Ty, VUniv) =
    val (ety, vt, vu) = infer(tm)
    (ety, vt)

  private def check(tm: S.Tm, ty: Option[S.Ty])(implicit
      ctx: Ctx
  ): (Tm, Ty, VTy, VUniv) = ty match
    case Some(ty) =>
      val ety = checkType(ty)
      val vty = ctx.eval(ety)
      val etm = check(tm, vty)
      (etm, ety, vty)
    case None =>
      val (etm, vty) = infer(tm)
      (etm, ctx.quote(vty), vty)

  private def check(tm: S.Tm, ty: VTy, univ: VUniv)(implicit ctx: Ctx): Tm =
    if !tm.isPos then debug(s"check $tm : ${ctx.pretty(ty)}")
    (tm, force(ty)) match
      case (S.Pos(pos, tm), _) => check(tm, ty)(ctx.enter(pos))

      case (S.Lam(x, i, ot, b), VPi(y, i2, a, rt)) if icitMatch(i, y, i2) =>
        ot.foreach(t0 => {
          val ety = checkType(t0)
          unify(ctx.eval(ety), a)
        })
        val eb = check(b, ctx.inst(rt))(ctx.bind(x, a))
        Lam(x, i2, eb)
      case (S.Var(x), VPi(_, Impl, _, _)) if hasMetaType(x) =>
        val Some((ix, varty)) = ctx.lookup(x): @unchecked
        unify(varty, ty)
        Var(ix)
      case (tm, VPi(x, Impl, a, b)) =>
        val etm = check(tm, ctx.inst(b))(ctx.bind(x, a, true))
        Lam(x, Impl, etm)

      case (S.Pair(fst, snd), VSigma(_, a, b)) =>
        val efst = check(fst, a)
        val esnd = check(snd, b(ctx.eval(efst)))
        Pair(efst, esnd)

      case (S.Let(x, t, v, b), _) =>
        val (ev, et, vt) = check(v, t)
        val eb = check(b, ty)(ctx.define(x, vt, et, ctx.eval(ev), ev))
        Let(x, et, ev, eb)
      case (S.Hole(ox), _) =>
        val t = newMeta(ty)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, ty))
        t
      case _ =>
        val (etm, ty2) = insert(infer(tm))
        unify(ty2, ty)
        etm

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

  private def infer(tm: S.Tm)(implicit ctx: Ctx): (Tm, VTy, VUniv) =
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))
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
                  case Some(e) => (Global(x), e.vty, e.vuniv)
                  case None    => error(s"undefined variable $x")
      case S.Let(x, t, v, b) =>
        val (ev, et, vt) = check(v, t)
        val (eb, rt) = infer(b)(ctx.define(x, vt, et, ctx.eval(ev), ev))
        (Let(x, et, ev, eb), rt)
      case S.Hole(ox) =>
        val top = ctx.eval(newMeta(VMetaTy()))
        val u = ctx.eval(newMeta(top))
        val a = ctx.eval(newMeta(u))
        val t = newMeta(a)
        ox.foreach(x => holes += x -> HoleEntry(ctx, t, a, u))
        (t, a, u)
      case S.Pi(x, i, a, b) =>
        val ea = checkType(a)
        val eb = checkType(b)(ctx.bind(x, ctx.eval(ea)))
        (Pi(x, i, ea, eb), VType())
      case S.Sigma(x, a, b) =>
        val ea = checkType(a)
        val eb = checkType(b)(ctx.bind(x, ctx.eval(ea)))
        (Sigma(x, ea, eb), VType())
      case S.Pair(fst, snd) =>
        val (efst, fstty, u1) = infer(fst)
        val (esnd, sndty, u2) = infer(snd)
        (
          Pair(efst, esnd),
          VSigma(DontBind, fstty, CFun(_ => sndty)),
          sigmaUniv(u1, u2)
        )
      case S.Lam(x, S.ArgIcit(i), mty, b) =>
        val pty = mty match
          case Some(ty) =>
            val ety = checkType(ty)
            ctx.eval(ety)
          case None =>
            val m = newMeta(VType())
            ctx.eval(m)
        val ctx2 = ctx.bind(x, pty)
        val (eb, rty) = insert(infer(b)(ctx2))(ctx2)
        (Lam(x, i, eb), VPi(x, i, pty, ctx.close(rty)))
      case S.Lam(_, S.ArgNamed(_), _, _) => error(s"cannot infer: $tm")
      case S.App(f, a, i) =>
        val (icit, ef, fty) = i match
          case S.ArgNamed(x) =>
            val (ef, fty) = insertPi(infer(f), Until(x))
            (Impl, ef, fty)
          case S.ArgIcit(Impl) =>
            val (ef, fty) = infer(f)
            (Impl, ef, fty)
          case S.ArgIcit(Expl) =>
            val (ef, fty) = insertPi(infer(f))
            (Expl, ef, fty)
        val (pty, rty) = force(fty) match
          case VPi(x, icit2, pty, rty) =>
            if icit != icit2 then error(s"icit mismatch: $tm")
            (pty, rty)
          case _ =>
            val pty = ctx.eval(newMeta(VType()))
            val x = DoBind(Name("x"))
            val rty = CClos(ctx.env, newMeta(VType())(ctx.bind(x, pty)))
            unify(fty, VPi(x, icit, pty, rty))
            (pty, rty)
        val ea = check(a, pty)
        (App(ef, ea, icit), rty(ctx.eval(ea)))
      case S.Proj(t, p) =>
        val (et, ty) = insertPi(infer(t))
        (force(ty), p) match
          case (_, S.Named(x)) =>
            val (p, pty) = projNamed(ctx.eval(et), ty, x)
            (Proj(et, p), pty)
          case (VSigma(_, fstty, _), S.Fst) => (Proj(et, Fst), fstty)
          case (VSigma(_, _, sndty), S.Snd) =>
            (Proj(et, Snd), sndty(vfst(ctx.eval(et))))
          case (tty, S.Fst) =>
            val pty = ctx.eval(newMeta(VType()))
            val rty =
              CClos(ctx.env, newMeta(VType())(ctx.bind(DoBind(Name("x")), pty)))
            unify(tty, VSigma(DoBind(Name("x")), pty, rty))
            (Proj(et, Fst), pty)
          case (tty, S.Snd) =>
            val pty = ctx.eval(newMeta(VType()))
            val rty =
              CClos(ctx.env, newMeta(VType())(ctx.bind(DoBind(Name("x")), pty)))
            unify(tty, VSigma(DoBind(Name("x")), pty, rty))
            (Proj(et, Snd), rty(vfst(ctx.eval(et))))

  private def prettyHoles(implicit ctx0: Ctx): String =
    holes
      .map((x, e) =>
        e match
          case HoleEntry(ctx, tm, vty) =>
            s"_$x : ${ctx.pretty(vty)} = ${ctx.pretty(tm)}\nlocals:\n${ctx.prettyLocals}"
      )
      .mkString("\n\n")

  def elaborate(tm: S.Tm, ty: Option[S.Ty] = None)(implicit
      ctx: Ctx
  ): (Tm, Ty) =
    resetMetas()
    holes.clear()

    val (etm_, ety_, _) = check(tm, ty)
    val etm = ctx.zonk(etm_)
    val ety = ctx.zonk(ety_)

    debug(s"elaborated ${ctx.pretty(etm)} : ${ctx.pretty(ety)}")
    if holes.nonEmpty then
      error(
        s"holes found: ${ctx.pretty(etm)} : ${ctx.pretty(ety)}\n\n${prettyHoles}"
      )
    val ums = unsolvedMetas()
    if ums.nonEmpty then
      error(
        s"unsolved metas: ${ctx.pretty(etm)} : ${ctx
            .pretty(ety)}\n${ums.map((id, ty) => s"?$id : ${ctx.pretty(ty)}").mkString("\n")}"
      )
    (etm, ety)

  def elaborate(d: S.Def): Def =
    debug(s"elaborate $d")
    d match
      case S.DDef(x, t, v) =>
        implicit val ctx: Ctx = Ctx.empty()
        if getGlobal(x).isDefined then error(s"duplicate global $x")
        val (etm, ety) = elaborate(v, t)
        setGlobal(GlobalEntry(x, etm, ety, eval(etm)(Nil), eval(ety)(Nil)))
        val ed = DDef(x, ety, etm)
        debug(s"elaborated $ed")
        ed

  def elaborate(ds: S.Defs): Defs = Defs(ds.toList.map(elaborate))
