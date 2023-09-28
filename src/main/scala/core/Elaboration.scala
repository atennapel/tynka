package core

import common.Common.*
import common.Debug.*
import surface.Syntax as S
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*
import Globals.*
import Ctx.*

import scala.annotation.tailrec
import scala.collection.mutable
import surface.Syntax.Def

object Elaboration extends RetryPostponed:
  private val unification = new Unification(this)

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
    debug(s"unify1 ${ctx.pretty1(a)} ~ ${ctx.pretty1(b)}")
    try unification.unify1(a, b)(ctx.lvl)
    catch
      case err: UnifyError =>
        error(
          s"failed to unify ${ctx.pretty1(a)} ~ ${ctx.pretty1(b)}: ${err.msg}"
        )

  // metas
  private def closeTy(ty: Ty)(implicit ctx: Ctx): Ty =
    def go(ls: Locals, xs: List[Bind], ty: Ty): Ty = (ls, xs) match
      case (LEmpty, Nil) => ty
      case (LDef(ls, a, v), DoBind(x) :: xs) =>
        go(ls, xs, Let1(x, a, v, ty))
      case (LBind0(ls, a, cv), x :: xs) =>
        go(ls, xs, MetaPi(false, a, ty))
      case (LBind1(ls, a), x :: xs) => go(ls, xs, MetaPi(true, a, ty))
      case _                        => impossible()
    go(ctx.locals, ctx.binds, ty)

  private def freshMetaId(ty: VTy)(implicit ctx: Ctx): MetaId =
    val qa = closeTy(ctx.quote1(ty, UnfoldNone))
    val vqa = eval1(qa)(EEmpty)
    val m = newMeta(Set.empty, vqa)
    debug(s"freshMetaId ?$m : ${ctx.pretty1(ty)}")
    m

  private inline def freshMeta(ty: VTy)(implicit ctx: Ctx): Tm1 =
    AppPruning(freshMetaId(ty), ctx.pruning)

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
      debug(
        s"coe ${ctx.pretty1(t)} from ${ctx.pretty1(a1)} to ${ctx.pretty1(a2)}"
      )
      (forceAll1(a1), forceAll1(a2)) match
        case (VFlex(x, sp), _) => unify1(a1, a2); None
        case (_, VFlex(x, sp)) => unify1(a1, a2); None

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

        case (VLift(_, VFun(a, cv, b)), _) =>
          Some(coe(quoteFun(a, t), liftFun(a, b, cv), a2))
        case (_, VLift(_, VFun(t1, cv, t2))) =>
          Some(spliceFun(t1, coe(t, a1, liftFun(t1, t2, cv))))

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

        case (_, _) => unify1(a1, a2); None

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
        val vbcv2 = ctx.eval1(freshCV())
        val b2 = ctx.eval1(freshMeta(VU0(vbcv2)))
        unify1(a, VFun(a2, vbcv2, b2))
        (a2, vbcv2, b2)

  private def ensureLift(t: VTy)(implicit ctx: Ctx): (VCV, VTy) =
    forceAll1(t) match
      case VLift(cv, ty) => (cv, ty)
      case _ =>
        val cv = ctx.eval1(freshCV())
        val ty = ctx.eval1(freshMeta(VU0(cv)))
        unify1(t, VLift(cv, ty))
        (cv, ty)

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

  // postponing
  private def closeTm(tm: Tm1)(implicit ctx: Ctx): Tm1 =
    def go(ls: Locals, xs: List[Bind], tm: Tm1): Tm1 = (ls, xs) match
      case (LEmpty, Nil) => tm
      case (LDef(ls, a, v), DoBind(x) :: xs) =>
        go(ls, xs, Let1(x, a, v, tm))
      case (LBind0(ls, a, cv), x :: xs) =>
        go(ls, xs, MetaLam(false, tm))
      case (LBind1(ls, a), x :: xs) => go(ls, xs, MetaLam(true, tm))
      case _                        => impossible()
    go(ctx.locals, ctx.binds, tm)

  private def unifyPlaceholder(m: MetaId, tm: Tm1)(implicit ctx: Ctx): Unit =
    getMeta(m) match
      case Unsolved(blocking, ty) =>
        val solution = closeTm(tm)
        solveMeta(m, eval1(solution)(EEmpty))
        blocking.foreach(id => retryPostponed(postponedId(id)))
      case Solved(v, _) =>
        unify1(ctx.eval1(tm), vappPruning(v, ctx.pruning)(ctx.env))

  override def retryPostponed(id: PostponedId): Unit =
    getPostponed(id) match
      case PECheck1(ctx_, tm, ty, m) =>
        debug(
          s"retryPostponed ?p$id as ?$m: check1 $tm : ${ctx_.pretty1(ty)}"
        )
        forceAll1(ty) match
          case VFlex(m2, _) => addBlocking(id, m2)
          case _ =>
            implicit val ctx: Ctx = ctx_
            val etm = check1(tm, ty)
            unifyPlaceholder(m, etm)
            setPostponed(id, PECheck1Done(ctx, Some(etm)))
      case PECheckVarU1(ctx_, x, ty, m) =>
        debug(
          s"retryPostponed ?p$id as ?$m: check1 $x : ${ctx_.pretty1(ty)}"
        )
        implicit val ctx: Ctx = ctx_
        val Some(Name1(_, vty)) = ctx.lookup(x): @unchecked
        forceAll1(vty) match
          case VFlex(m2, _) => addBlocking(id, m2)
          case _ =>
            val etm = check1(S.Var(x), ty)
            unifyPlaceholder(m, etm)
            setPostponed(id, PECheck1Done(ctx, Some(etm)))
      case _ => ()

  private def retryAllPostponed(): Unit =
    @tailrec
    def go(id: PostponedId): Unit =
      if id < nextPostponedId then
        inline def checkAgain(ctx0: Ctx, tm: S.Tm, ty: VTy, m: MetaId): Unit =
          implicit val ctx: Ctx = ctx0
          debug(
            s"retryAllPostponed ?p$id as ?$m: check1 $tm : ${ctx.pretty1(ty)}"
          )
          val (etm, vty) = insert(infer1(tm))
          setPostponed(id, PECheck1Done(ctx, None)) // prevent retry
          val etm2 = coe(etm, vty, ty)
          setPostponed(id, PECheck1Done(ctx, Some(etm2)))
          unifyPlaceholder(m, etm2)
        getPostponed(id) match
          case PECheck1(ctx_, tm, ty, m)    => checkAgain(ctx_, tm, ty, m)
          case PECheckVarU1(ctx_, x, ty, m) => checkAgain(ctx_, S.Var(x), ty, m)
          case _                            => ()
        go(id + 1)
      else ()
    go(postponedId(0))

  // checking
  private def checkMatch(
      scrut: Either[(Tm0, VTy), S.Tm],
      cs: List[(PosInfo, Name, List[Bind], S.Tm)],
      other: Option[(PosInfo, S.Tm)],
      vrty: VTy,
      vrcv: VTy
  )(implicit ctx: Ctx): Tm0 =
    val (escrut, vscrutty) = scrut match
      case Left(p) => p
      case Right(scrut) =>
        val vscrutty = ctx.eval1(freshMeta(VU0(VVal)))
        val escrut = check0(scrut, vscrutty, VVal)
        (escrut, vscrutty)
    forceAll1(vscrutty) match
      case VData(dx, dcs) =>
        val used = mutable.Set[Name]()
        val cons = dcs.tm.map(_.name).toSet
        val ecs = cs.map { case (pos, cx, ps, b) =>
          implicit val ctx1: Ctx = ctx.enter(pos)
          if !cons.contains(cx) then
            error(s"$cx is not a constructor of type $dx")
          if used.contains(cx) then
            error(s"constructor appears twice in match $cx")
          used += cx
          val tas = dcs.tm
            .find(c => c.name == cx)
            .get
            ._2
            .map(_._2)
            .map { t =>
              val vt = eval1(t)(E1(dcs.env, vscrutty))
              (vt, ctx1.quote1(vt))
            }
          if ps.size != tas.size then
            error(
              s"datatype argument size mismatch, expected ${tas.size} but got ${ps.size}"
            )
          val tps = ps.zip(tas)
          val pctx = tps.foldLeft(ctx1) { case (ctx, (x, (vt, qt))) =>
            ctx.bind0(x, qt, vt, Val, VVal)
          }
          val eb = check0(b, vrty, vrcv)(pctx)
          val lams = tps.foldRight(eb) { case ((x, (_, qt)), b) =>
            Lam0(x, qt, b)
          }
          (cx, lams)
        }
        val left = cons -- used
        if other.isEmpty && left.nonEmpty then
          error(
            s"non-exhaustive match, constructors left: ${left.mkString(" ")}"
          )
        val eother = other.map { (pos, b) =>
          implicit val ctxOther: Ctx = ctx.enter(pos)
          if left.isEmpty then error(s"other case does not match anything")
          check0(b, vrty, vrcv)
        }
        Match(escrut, ecs, eother)
      case _ =>
        error(
          s"expected a datatype in match but got ${ctx.pretty1(vscrutty)}"
        )

  private def check0(tm: S.Tm, ty: VTy, cv: VCV)(implicit ctx: Ctx): Tm0 =
    if !tm.isPos then
      debug(s"check0 $tm : ${ctx.pretty1(ty)} : ${ctx.pretty1(cv)}")
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

      case S.Con(x, args) =>
        unify1(cv, VVal)
        forceAll1(ty) match
          case VData(_, cs) =>
            cs.tm.find(c => c.name == x) match
              case None =>
                error(s"constructor $x not found in ${ctx.pretty1(ty)}")
              case Some(DataCon(_, args2)) =>
                if args.size != args2.size then
                  error(
                    s"invalid amount of arguments for constructor, expected ${args2.size} but got ${args.size}"
                  )
                val eargs = args.zip(args2).map { case (arg, (_, t)) =>
                  check0(arg, eval1(t)(E1(cs.env, ty)), VVal)
                }
                Con(x, eargs)
          case _ => error(s"expected datatype but got ${ctx.pretty1(ty)}")

      case S.Match(Some(scrut), cs, other) =>
        checkMatch(Right(scrut), cs, other, ty, cv)
      case S.Match(None, cs, other) =>
        val (t1, fcv, t2) = ensureFun(ty, cv)
        val qt1 = ctx.quote1(t1)
        val x = DoBind(Name("x"))
        val etm = checkMatch(Left((Var0(ix0), t1)), cs, other, t2, fcv)(
          ctx.insert0(x, qt1, Val)
        )
        Lam0(x, qt1, etm)

      case S.Hole(_) => splice(freshMeta(VLift(cv, ty)))

      case S.Splice(t) => splice(check1(t, VLift(cv, ty)))

      case tm =>
        infer(tm) match
          case Infer0(etm, vty, vcv) =>
            unify1(vcv, cv)
            unify1(vty, ty)
            etm
          case Infer1(etm, vty) =>
            val (etm2, vty2) = insert((etm, vty))
            coeQuote(etm2, vty2, ty, cv)

  private def icitMatch(i: S.ArgInfo, x: Bind, i2: Icit): Boolean = i match
    case S.ArgNamed(y) =>
      x match
        case DontBind  => false
        case DoBind(x) => x == y
    case S.ArgIcit(i) => i == i2

  private def varHasUnknownType1(x: Name)(implicit ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some(Name1(_, ty)) =>
        forceAll1(ty) match
          case VFlex(_, _) => true
          case _           => false
      case _ => false

  private def check1(tm: S.Tm, ty: VTy)(implicit ctx: Ctx): Tm1 =
    if !tm.isPos then debug(s"check1 $tm : ${ctx.pretty1(ty)}")
    (tm, forceAll1(ty)) match
      case (S.Pos(pos, tm), _) => check1(tm, ty)(ctx.enter(pos))

      case (S.Lam(x, i, ma, b), VPi(x2, i2, t1, t2)) if icitMatch(i, x2, i2) =>
        ma.foreach { sty => unify1(ctx.eval1(check1(sty, VU1)), t1) }
        val qt1 = ctx.quote1(t1)
        Lam1(x, i2, qt1, check1(b, t2(VVar1(ctx.lvl)))(ctx.bind1(x, qt1, t1)))

      case (S.Var(x), VPi(_, Impl, _, _)) if varHasUnknownType1(x) =>
        val Some(Name1(lvl, ty2)) = ctx.lookup(x): @unchecked
        unify1(ty2, ty)
        Var1(lvl.toIx(ctx.lvl))

      case (S.Var(x), VU1) if varHasUnknownType1(x) =>
        val Some(Name1(_, ty2)) = ctx.lookup(x): @unchecked
        val VFlex(m, _) = forceAll1(ty2): @unchecked
        val placeholder = freshMetaId(ty)
        val pid = newPostponed(PECheckVarU1(ctx, x, ty, placeholder))
        addBlocking(pid, m)
        debug(
          s"postpone ?p$pid as ?$placeholder: check1 $tm : ${ctx.pretty1(ty)}"
        )
        PostponedCheck1(pid)

      case (tm, VPi(x, Impl, t1, t2)) =>
        val qt1 = ctx.quote1(t1)
        Lam1(x, Impl, qt1, check1(tm, t2(VVar1(ctx.lvl)))(ctx.insert1(x, qt1)))

      case (S.Match(None, cs, o), VPi(x, Expl, t1, t2)) =>
        val qt1 = ctx.quote1(t1)
        val y = x match
          case DontBind => DoBind(Name("x"))
          case x        => x
        val nctx = ctx.insert1(y, qt1)
        val (vscrutcv, vscrutty) = ensureLift(t1)
        val (vrcv, vrty) = ensureLift(t2(VVar1(ctx.lvl)))(nctx)
        unify1(vscrutcv, VVal)
        val escrut = Left((Splice(Var1(ix0)), vscrutty))
        val ematch = checkMatch(escrut, cs, o, vrty, vrcv)(nctx)
        Lam1(y, Expl, qt1, Quote(ematch))

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

      case (tm, VFlex(m, sp)) =>
        val placeholder = freshMetaId(ty)
        val pid = newPostponed(PECheck1(ctx, tm, ty, placeholder))
        addBlocking(pid, m)
        debug(
          s"postpone ?p$pid as ?$placeholder: check1 $tm : ${ctx.pretty1(ty)}"
        )
        PostponedCheck1(pid)

      case (tm, _) =>
        val (etm, vty) = insert(infer1(tm))
        coe(etm, vty, ty)

  // inference
  private def infer0(tm: S.Tm)(implicit ctx: Ctx): (Tm0, VTy, VCV) =
    if !tm.isPos then debug(s"infer0 $tm")
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
    if !tm.isPos then debug(s"infer1 $tm")
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
    if !tm.isPos then debug(s"infer $tm")
    tm match
      case S.Pos(pos, tm) => infer(tm)(ctx.enter(pos))

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

      case S.Hole(_)   => error("cannot infer hole")
      case S.Con(_, _) => error("cannot infer con")

      case S.Data(x, cs) =>
        val conNames = cs.map(c => c.name)
        if conNames.size != conNames.distinct.size then
          error("duplicate constructor names")
        val newctx = ctx.bind1(x, U0(Val), VU0(VVal))
        val ecs = cs.map { case S.DataCon(pos, cx, args) =>
          implicit val newctx2 = newctx.enter(pos)
          val eargs = args.map((ax, sty) => (ax, check1(sty, VU0(VVal))))
          DataCon(cx, eargs)
        }
        Infer1(Data(x, ecs), VU0(VVal))

      case S.Match(Some(scrut), cs, other) =>
        val cv = ctx.eval1(freshCV())
        val ty = ctx.eval1(freshMeta(VU0(cv)))
        val etm = checkMatch(Right(scrut), cs, other, ty, cv)
        Infer0(etm, ty, cv)
      case m @ S.Match(None, cs, other) =>
        val cv = ctx.eval1(freshCV())
        val t1 = ctx.eval1(freshMeta(VU0(VVal)))
        val t2 = ctx.eval1(freshMeta(VU0(cv)))
        val fun = VFun(t1, cv, t2)
        val etm = check0(m, fun, VComp)
        Infer0(etm, fun, VComp)

  // elaboration
  def elaborate(d: S.Def): Unit = d match
    case S.DDef(pos, x, rec, m, mty, v) =>
      implicit val ctx: Ctx = Ctx.empty(pos)
      if getGlobal(x).isDefined then error(s"duplicated definition $x")
      val entry = if m then
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
        GlobalEntry1(x, ev, ty, vv, vty)
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
        GlobalEntry0(x, ev, ty, cv, ctx.eval0(ev), vty, vcv)
      retryAllPostponed()
      val ums = unsolvedMetas()
      if ums.nonEmpty then
        val str =
          ums.map((id, ty) => s"?$id : ${ctx.pretty1(ty)}").mkString("\n")
        error(s"there are unsolved metas:\n$str")
      setGlobal(entry)

  def elaborate(d: S.Defs): Unit = d.toList.foreach(elaborate)
