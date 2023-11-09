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
import surface.Syntax.Pat
import surface.Syntax.DataCon

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
  private def liftFun(lev: VTy, a: VTy, b: VTy, bcv: VCV)(implicit
      ctx: Ctx
  ): VTy =
    implicit val l = ctx.lvl + 1
    val qbcv = quote1(bcv, UnfoldNone)
    val qb = quote1(b, UnfoldNone)
    VPi(DontBind, Expl, VLift(VVal(lev), a), Clos(ctx.env, Lift(qbcv, qb)))

  private def quoteFun(x: Bind, lev: VTy, a: VTy, t: Tm1)(implicit
      ctx: Ctx
  ): Tm1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    Lam1(
      DoBind(y),
      Expl,
      Lift(Val(ctx.quote1(lev)), ctx.quote1(a)),
      Quote(App0(Wk10(splice(t)), Splice(Var1(ix0))))
    )

  private def spliceFun(x: Bind, a: VTy, t: Tm1)(implicit
      ctx: Ctx
  ): Tm1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    Quote(
      Lam0(
        DoBind(y),
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

        case (VLift(_, VFun(lev, a, cv, b)), VPi(x, _, _, _)) =>
          Some(coe(quoteFun(x, lev, a, t), liftFun(lev, a, b, cv), a2))
        case (VLift(_, VFun(lev, a, cv, b)), _) =>
          Some(coe(quoteFun(DontBind, lev, a, t), liftFun(lev, a, b, cv), a2))
        case (VPi(x, _, _, _), VLift(_, VFun(lev, t1, cv, t2))) =>
          Some(spliceFun(x, t1, coe(t, a1, liftFun(lev, t1, t2, cv))))
        case (_, VLift(_, VFun(lev, t1, cv, t2))) =>
          Some(spliceFun(DontBind, t1, coe(t, a1, liftFun(lev, t1, t2, cv))))

        case (pi @ VPi(x, Expl, a, b), VLift(cv, a2)) =>
          unify1(cv, VComp)
          val lev = ctx.eval1(freshMeta(VLevity))
          val a1 = ctx.eval1(freshMeta(VU0(VVal(lev))))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2_ = ctx.eval1(freshMeta(VU0(va2cv)))
          val fun = VFun(lev, a1, va2cv, a2_)
          unify1(a2, fun)
          go(t, pi, VLift(VComp, fun))
        case (VLift(cv, a), pi @ VPi(x, Expl, t1, t2)) =>
          unify1(cv, VComp)
          val lev = ctx.eval1(freshMeta(VLevity))
          val a1 = ctx.eval1(freshMeta(VU0(VVal(lev))))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2 = ctx.eval1(freshMeta(VU0(va2cv)))
          val fun = VFun(lev, a1, va2cv, a2)
          unify1(a, fun)
          go(t, VLift(VComp, fun), pi)

        case (_, _) => unify1(a1, a2); None

    go(t, a1, a2).getOrElse(t)

  // helpers
  private def tyAnnot(ma: Option[S.Tm], ty: VTy)(implicit ctx: Ctx): Ty =
    ma.fold(freshMeta(ty))(a => check1(a, ty))

  private def ensureFun(a: VTy, acv: VCV)(implicit
      ctx: Ctx
  ): (VTy, VTy, VCV, VTy) =
    forceAll1(a) match
      case VFun(l, a, bcv, b) => (l, a, bcv, b)
      case _ =>
        unify1(acv, VComp)
        val lev = ctx.eval1(freshMeta(VLevity))
        val a2 = ctx.eval1(freshMeta(VU0(VVal(lev))))
        val vbcv2 = ctx.eval1(freshCV())
        val b2 = ctx.eval1(freshMeta(VU0(vbcv2)))
        unify1(a, VFun(lev, a2, vbcv2, b2))
        (lev, a2, vbcv2, b2)

  private def ensureFunN(n: Int, a: VTy, acv: VCV)(implicit
      ctx: Ctx
  ): (List[(VTy, VTy)], VCV, VTy) =
    if n == 0 then (Nil, acv, a)
    else
      val (lev, t1, cv, t2) = ensureFun(a, acv)
      val (ps, rcv, rt) = ensureFunN(n - 1, t2, cv)
      ((lev, t1) :: ps, rcv, rt)

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
  ): Infer =
    debug(s"apply1 ${ctx.pretty1(a)} $i @ $u")
    forceAll1(a) match
      case VPi(x, i2, a, b) =>
        if i != i2 then error(s"icit mismatch in apply1")
        val u2 = check1(u, a)
        Infer1(App1(t, u2, i), b(ctx.eval1(u2)))
      case VLift(_, VFun(lev, a, bcv, b)) =>
        if i != Expl then error(s"icit mismatch in apply1")
        val u2 = check0(u, a, VVal(lev))
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

  // pattern matching
  private final case class Clause(
      pos: PosInfo,
      vars: Map[Lvl, S.Pat],
      lets: List[(Name, VTy, VTy, Lvl)],
      guard: Option[S.Tm],
      body: Either[Lvl, S.Tm]
  ):
    override def toString: String =
      val m = vars.toList.map((l, p) => s"$l -> $p").mkString(", ")
      val g = guard.map(g => s" if $g").getOrElse("")
      val ls = lets match
        case Nil => ""
        case _ =>
          s"let ${lets.map((x, _, _, l) => s"$x = '$l").mkString("; ")}; "
      val b = body match
        case Left(l)  => s"'$l"
        case Right(t) => s"$t"
      s"($m)$g => $ls$b"

  private final case class VarInfo(lev: VTy, ty: VTy, matchedCons: Set[Name]):
    def matchOn(cx: Name): VarInfo = VarInfo(lev, ty, matchedCons + cx)
  private enum CaseTree:
    case Test(
        x: Lvl,
        ty: VTy,
        con: Name,
        joins: List[(Name, Ty, CV, Tm0)],
        lams: List[(Bind, Ty)],
        params: List[VTy],
        yes: CaseTree,
        no: CaseTree
    )
    case Run(tm: Tm0)
    case Guard(condition: Tm0, ifTrue: Tm0, ifFalse: CaseTree)
    case Exhausted(ty: VTy)
  import CaseTree.*
  private enum Choice:
    case Yes(clause: Clause)
    case No(clause: Clause)
    case Both(clause: Clause)
  import Choice.*

  private def compileTree(t: CaseTree)(implicit lvl: Lvl): Tm0 = t match
    case Exhausted(ty) => Impossible(quote1(ty, UnfoldNone)(lvl))
    case Run(tm)       => tm
    case Guard(cond, ifTrue, ifFalse) =>
      Match(
        cond,
        tbool,
        Name("True"),
        Nil,
        ifTrue,
        compileTree(ifFalse)
      )
    case Test(x, ty, con, joins, lams, ps, yes, no) =>
      val inneryes = compileTree(yes)(lvl + joins.size + lams.size)
      val eyes = lams.foldRight(inneryes) { case ((x, t), b) => Lam0(x, t, b) }
      val eno = compileTree(no)(lvl + joins.size)
      val innerlvl = lvl + joins.size
      val inner =
        Match(
          Var0(x.toIx(innerlvl)),
          quote1(ty, UnfoldNone)(innerlvl),
          con,
          ps.map(p => quote1(p, UnfoldNone)(innerlvl)),
          eyes,
          eno
        )
      joins.foldRight(inner) { case ((x, t, _, v), b) =>
        Let0(x, t, v, b)
      }

  private def normalizePat(p: S.Pat)(implicit ctx: Ctx): S.Pat =
    p match
      case S.PCon(cx, x, args) => S.PCon(cx, x, args)
      case S.PVar(DontBind)    => S.PVar(DontBind)
      case S.PVar(b @ DoBind(x)) =>
        getGlobal(x) match
          case Some(GlobalCon0(_, _, _)) => S.PCon(x, DontBind, Nil)
          case Some(GlobalData0(_, _, _, _, _)) =>
            error(s"datatype in pattern: $x")
          case _ => S.PVar(b)

  private def checkMatch(
      scrut: Either[List[(Tm0, VTy, VTy, VCV)], List[S.Tm]],
      pats: List[(PosInfo, List[S.Pat], Option[S.Tm], S.Tm)],
      vrty: VTy,
      vrcv: VTy
  )(implicit ctx: Ctx): Tm0 =
    debug(s"checkMatch : ${ctx.pretty1(vrty)}")
    val escruts = scrut match
      case Left(p) => p
      case Right(ss) =>
        ss.map { scrut =>
          val lev = ctx.eval1(freshMeta(VLevity))
          val cv = VVal(lev)
          val vscrutty = ctx.eval1(freshMeta(VU0(cv)))
          val escrut = check0(scrut, vscrutty, cv)
          (escrut, lev, vscrutty, cv)
        }

    escruts.foreach { (_, _, ty, _) =>
      forceAll1(ty) match
        case VFlex(_, _) =>
          // TODO: postpone check
          error(s"scrutinee in match with flex type: ${ctx.pretty1(ty)}")
        case _ =>
    }

    if escruts.isEmpty then impossible()
    if pats.isEmpty then
      escruts.foreach { (escrut, _, vscrutty, vcv) =>
        forceAll1(vscrutty) match
          case VTConApp(x, _) =>
            val GlobalData0(_, _, _, _, cs) = getGlobalData0(x)
            if cs.isEmpty then ()
            else
              error(
                s"empty match with non-void type: ${ctx.pretty1(vscrutty)}"
              )
          case _ =>
            error(s"empty match with non-void type: ${ctx.pretty1(vscrutty)}")
      }
      return Impossible(ctx.quote1(vrty))

    val (nctx, varInfo, lets) =
      escruts.zipWithIndex.foldLeft(
        (ctx, Map.empty[Lvl, VarInfo], List.empty[(Name, Ty, Tm0)])
      ) { case ((ctx, varInfo, lets), ((escrut, lev, vscrutty, vcv), i)) =>
        val x = Name(s"scrut$i")
        val scrutty = ctx.quote1(vscrutty)
        val qescrut = escrut.wk0N(i)
        (
          ctx.insert0(DoBind(x), scrutty, ctx.quote1(vcv)),
          varInfo + (ctx.lvl -> VarInfo(lev, vscrutty, Set.empty)),
          lets ++ List((x, scrutty, qescrut))
        )
      }
    val tree = genMatch(
      pats.map((pos, ps, guard, tm) =>
        if ps.size != escruts.size then
          error(s"pattern amount mismatch")(nctx.enter(pos))
        val norm =
          escruts.zip(ps).zipWithIndex.map {
            case (((_, _, vscrutty, _), pat), i) =>
              (ctx.lvl + i, normalizePat(pat)(ctx.enter(pos)))
          }
        Clause(
          pos,
          norm.toMap,
          Nil,
          guard,
          Right(tm)
        )
      ),
      vrty,
      vrcv
    )(nctx, varInfo)
    val ctree = compileTree(tree)(nctx.lvl)
    val qrt = ctx.quote1(vrty)
    val res = lets.foldRight(ctree) { case ((x, ty, v), b) =>
      Let0(x, ty, v, b)
    }
    res

  private def simplifyClause(c: Clause)(implicit
      varInfo: Map[Lvl, VarInfo]
  ): Clause =
    c match
      case Clause(pos, vars, lets, guard, tm) =>
        val nlets = mutable.ArrayBuffer.empty[(Name, VTy, VTy, Lvl)]
        val rest = vars.flatMap { (lvl, p) =>
          p match
            case S.PVar(DontBind) => None
            case S.PVar(DoBind(x)) =>
              val info = varInfo(lvl)
              nlets += ((x, info.lev, info.ty, lvl))
              None
            case S.PCon(cx, DontBind, args) => Some(lvl -> p)
            case S.PCon(cx, DoBind(x), args) =>
              val info = varInfo(lvl)
              nlets += ((x, info.lev, info.ty, lvl))
              Some(lvl -> S.PCon(cx, DontBind, args))
        }
        Clause(
          pos,
          rest.toMap,
          lets ++ nlets,
          guard,
          tm
        )

  private def branchingHeuristic(
      pats: Map[Lvl, Pat],
      clauses: List[Clause]
  ): Lvl =
    pats.keys.maxBy(v =>
      clauses.count { case Clause(_, ps, _, _, _) => ps.contains(v) }
    )

  private def checkMatchBody(
      lets: List[(Name, VTy, VTy, Lvl)],
      body: Either[Lvl, S.Tm],
      vrty: VTy,
      vrcv: VCV
  )(implicit
      ctx: Ctx
  ): Tm0 =
    debug(
      s"checkMatchBody ${lets
          .map((x, _, t, l) => s"($x : ${ctx.pretty1(t)} = $l)")
          .mkString(" ")} $body : ${ctx.pretty1(vrty)}"
    )
    val (innerctx, ts) = lets.foldLeft((ctx, List.empty[(Ty, Ty)])) {
      case ((ctx, ts), (x, lev, vty, lvl)) =>
        val vlty = VLift(VVal(lev), vty)
        val ty = ctx.quote1(vty)
        val qlev = ctx.quote1(lev)
        val v = vquote(VVar0(lvl))
        (
          ctx.define(x, ctx.quote1(vlty), vlty, ctx.quote1(v), v),
          (qlev, ty) :: ts
        )
    }
    val ebody = body match
      case Left(lvl)   => innerctx.quote0(VVar0(lvl))
      case Right(body) => check0(body, vrty, vrcv)(innerctx)
    splice(lets.zip(ts.reverse).zipWithIndex.foldRight(quote(ebody)) {
      case ((((x, _, _, lvl), (lev, ty)), i), b) =>
        Let1(x, Lift(Val(lev), ty), Quote(Var0(lvl.toIx(ctx.lvl + i))), b)
    })

  private val tbool = TCon(Name("Bool"))
  private val vbool = VTCon(Name("Bool"))

  private def genMatch(
      clauses0: List[Clause],
      vrty: VTy,
      vrcv: VCV
  )(implicit ctx: Ctx, varInfo: Map[Lvl, VarInfo]): CaseTree =
    debug(s"genMatch ${clauses0.mkString(" | ")} : ${ctx.pretty1(vrty)}")
    if clauses0.isEmpty then impossible()
    val clauses = clauses0.map(simplifyClause)
    val Clause(pos, pats, lets, guard, body) = clauses.head
    if pats.isEmpty then
      val nctx = ctx.enter(pos)
      guard match
        case None =>
          return Run(checkMatchBody(lets, body, vrty, vrcv)(nctx))
        case _ if clauses.tail.isEmpty =>
          error("non-exhaustive pattern match")(nctx)
        case Some(g) =>
          val cond = checkMatchBody(
            lets,
            Right(g),
            vbool,
            VVal(VPrim1(Name("BoolRep")))
          )(nctx)
          val ifTrue = checkMatchBody(lets, body, vrty, vrcv)(nctx)
          val ifFalse = genMatch(clauses.tail, vrty, vrcv)
          return Guard(cond, ifTrue, ifFalse)
    val branchVar = branchingHeuristic(pats, clauses)
    val info = varInfo(branchVar)
    val dty = info.ty
    forceAll1(dty) match
      case VTConApp(dx, dpas) =>
        val GlobalData0(_, _, dps, _, csl) = getGlobalData0(dx)
        val cons = csl.toSet
        val S.PCon(cx, _, args) = pats(branchVar): @unchecked
        if info.matchedCons.contains(cx) then
          error(s"already matched on $cx of ${ctx.pretty1(dty)}")
        if !cons.contains(cx) then
          error(s"pattern $cx does not match type ${ctx.pretty1(dty)}")
        val GlobalCon0(_, _, dts) = getGlobalCon0(cx)
        if dts.size != args.size then error(s"pattern $cx arity mismatch")
        val ts = dts.map { (_, lev, t) =>
          val qlev = eval1(lev)(Env(dpas.map(_._1)))
          val ty = eval1(t)(Env(dpas.map(_._1)))
          (qlev, ty)
        }
        val nargs = args.map(normalizePat)
        val yes = mutable.ArrayBuffer.empty[Either[(Clause, List[Pat]), Clause]]
        val no = mutable.ArrayBuffer.empty[Clause]
        var nextctx = ctx
        val joins = mutable.ArrayBuffer.empty[(Name, Ty, CV, Tm0)]
        clauses.foreach { case c @ Clause(pos, pats, lets, guard, body) =>
          pats.get(branchVar) match {
            case Some(S.PCon(cx2, _, args2)) =>
              if cx == cx2 then {
                if args.size != args2.size then
                  error("invalid constructor arity")
                yes += Left((c, args2))
              } else no += c
            case None =>
              c.body match
                case Left(_) =>
                  yes += Right(c)
                  no += c
                case Right(_) =>
                  val jtm = checkMatchBody(c.lets, c.body, vrty, vrcv)(nextctx)
                  val lvl = ctx.lvl
                  val qty = nextctx.quote1(vrty)
                  val qcv = nextctx.quote1(vrcv)
                  val name = Name(s"j$lvl")
                  nextctx = nextctx.insert0(DoBind(name), qty, qcv)
                  joins += ((name, qty, qcv, jtm))
                  val newclause = Clause(c.pos, c.vars, Nil, c.guard, Left(lvl))
                  yes += Right(newclause)
                  no += newclause
            case _ => impossible()
          }
        }

        val vars = (0 until args.size).map(i => nextctx.lvl + i).toList
        val newVarInfo =
          vars.zip(ts).foldLeft(varInfo) { case (vars, (lvl, (lev, ty))) =>
            vars + (lvl -> VarInfo(lev, ty, Set.empty))
          }
        val yes2 = yes.map {
          case Right(c) => c
          case Left((c, args)) =>
            val newPats = vars.zip(args).map((lvl, p) => lvl -> normalizePat(p))
            Clause(
              pos,
              pats - branchVar ++ newPats,
              lets,
              guard,
              body
            )
        }

        val (yesctx, lams) =
          nargs
            .zip(ts)
            .zipWithIndex
            .foldLeft((nextctx, List.empty[(Bind, Ty)])) {
              case ((ctx, lams), ((p, (lev, ty)), i)) =>
                val x = p match
                  case S.PVar(b @ DoBind(x)) => b
                  case _                     => DoBind(Name(s"x$i"))
                val qty = ctx.quote1(ty)
                val qlev = ctx.quote1(lev)
                (ctx.insert0(x, qty, Val(qlev)), lams ++ List((x, qty)))
            }
        val yesResult =
          if yes.isEmpty then impossible()
          else genMatch(yes2.toList, vrty, vrcv)(yesctx, newVarInfo - branchVar)
        val matchedCons = info.matchedCons + cx
        val noResult =
          if no.isEmpty then
            if matchedCons == cons then Exhausted(vrty)
            else
              error(
                s"non-exhaustive pattern match, ${(cons -- matchedCons).mkString(", ")} left"
              )
          else if matchedCons == cons then Exhausted(vrty)
          else
            genMatch(no.toList, vrty, vrcv)(
              nextctx,
              varInfo + (branchVar -> info.matchOn(cx))
            )
        Test(
          branchVar,
          dty,
          cx,
          joins.toList,
          lams,
          ts.map(_._2),
          yesResult,
          noResult
        )
      case _ => error(s"expected a datatype but got ${ctx.pretty1(dty)}")

  // checking
  private def check0(tm: S.Tm, ty: VTy, cv: VCV)(implicit ctx: Ctx): Tm0 =
    if !tm.isPos then
      debug(s"check0 $tm : ${ctx.pretty1(ty)} : ${ctx.pretty1(cv)}")
    tm match
      case S.Pos(pos, tm) => check0(tm, ty, cv)(ctx.enter(pos))

      case S.Lam(x, i, ma, b) =>
        if i != S.ArgIcit(Expl) then error(s"implicit lambda in Ty")
        val (lev, t1, fcv, t2) = ensureFun(ty, cv)
        val qlev = ctx.quote1(lev)
        ma.foreach { sty => unify1(ctx.eval1(check1(sty, VU0(VVal(lev)))), t1) }
        val qt1 = ctx.quote1(t1)
        Lam0(
          x,
          qt1,
          check0(b, t2, fcv)(ctx.bind0(x, qt1, t1, Val(qlev), VVal(lev)))
        )

      case S.Let(x, rec, false, ma, v, b) =>
        val (ety, cv2, vcv2) =
          if rec then (tyAnnot(ma, VU0(VComp)), Comp, VComp)
          else
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(ma, VU0(vcv2))
            (ety, cv2, vcv2)
        val vty = ctx.eval1(ety)
        // if rec then ensureFun(vty, vcv2)
        val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
        val ev = check0(v, vty, vcv2)(if rec then nctx else ctx)
        val eb = check0(b, ty, cv)(nctx)
        if rec then LetRec(x, ety, ev, eb)
        else Let0(x, ety, ev, eb)

      case S.Match(Nil, ps) =>
        val size = if ps.isEmpty then 1 else ps.head._2.size
        val (ts, rcv, rt) = ensureFunN(size, ty, cv)
        val xs = (0 until size).map(i => DoBind(Name(s"scrut$i")))
        val scruts =
          (0 until size).reverse
            .zip(ts)
            .map { case (i, (lev, t)) => (Var0(mkIx(i)), lev, t, VVal(lev)) }
            .toList
        val (innerctx, qts) = xs.zip(ts).foldLeft((ctx, List.empty[Ty])) {
          case ((ctx, qts), (x, (lev, t))) =>
            val qlev = ctx.quote1(lev)
            val qt = ctx.quote1(t)
            (ctx.insert0(x, qt, Val(qlev)), qts ++ List(qt))
        }
        val etm = checkMatch(Left(scruts), ps, rt, rcv)(innerctx)
        xs.zip(qts).foldRight(etm) { case ((x, t), b) => Lam0(x, t, b) }
      case S.Match(scruts, ps) =>
        checkMatch(Right(scruts), ps, ty, cv)

      case S.Hole(_) => splice(freshMeta(VLift(cv, ty)))

      case S.Splice(t) => splice(check1(t, VLift(cv, ty)))

      case S.StringLit(v) =>
        unify1(cv, VVal(VPrim1(Name("Boxed"))))
        unify1(
          ty,
          VRigid(
            HPrim(Name("Class")),
            SApp(SId, VLabelLit("java.lang.String"), Expl)
          )
        )
        StringLit(v)

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

  private def checkLambdaMatch1(
      scrutCount: Int,
      ps: List[S.MatchCase],
      ty: VTy
  )(implicit
      ctx: Ctx
  ): Either[MetaId, Tm1] =
    debug(s"checkLambdaMatch1 $scrutCount : ${ctx.pretty1(ty)}")
    @tailrec
    def go(i: Int, ty: VTy, args: List[(Bind, VTy, VTy, Ty)])(implicit
        ctx: Ctx
    ): Either[MetaId, Tm1] =
      if i == 0 then
        val ixs = 0 until scrutCount
        val scruts = args.zip(ixs.reverse).map { case ((_, vt, lev, _), i) =>
          (Splice(Var1(mkIx(i))), lev, vt, VVal(lev))
        }
        val (vrcv, vrty) = ensureLift(ty)
        val ematch = checkMatch(Left(scruts), ps, vrty, vrcv)
        val lams = args.zip(ixs).foldRight(quote(ematch)) {
          case (((x, _, _, qt), i), b) => Lam1(x, Expl, qt, b)
        }
        Right(lams)
      else
        forceAll1(ty) match
          case VPi(x, Expl, t1, t2) =>
            val (vscrutcv, vscrutty) = ensureLift(t1)
            forceAll1(vscrutty) match
              case VFlex(m, _) => Left(m)
              case _ =>
                val qt1 = ctx.quote1(t1)
                val y = x match
                  case DontBind => DoBind(Name(s"x${scrutCount - i}"))
                  case x        => x
                val nctx = ctx.insert1(y, qt1)
                val lev = ctx.eval1(freshMeta(VLevity))
                unify1(vscrutcv, VVal(lev))
                go(
                  i - 1,
                  t2(VVar1(ctx.lvl)),
                  args ++ List((y, vscrutty, lev, qt1))
                )(
                  nctx
                )
          case VFlex(m, _) => Left(m)
          case _ => error(s"unexpected checking type ${ctx.pretty1(ty)}")
    go(scrutCount, ty, Nil)

  private def check1(tm: S.Tm, ty: VTy)(implicit ctx: Ctx): Tm1 =
    if !tm.isPos then debug(s"check1 $tm : ${ctx.pretty1(ty)}")
    (tm, forceAll1(ty)) match
      case (S.Pos(pos, tm), _) => check1(tm, ty)(ctx.enter(pos))

      case (S.Lam(x, i, ma, b), VPi(x2, i2, t1, t2)) if icitMatch(i, x2, i2) =>
        ma.foreach { sty => unify1(ctx.eval1(check1(sty, VU1)), t1) }
        val qt1 = ctx.quote1(t1)
        Lam1(x, i2, qt1, check1(b, t2(VVar1(ctx.lvl)))(ctx.bind1(x, qt1, t1)))

      case (S.Var(x, _), VPi(_, Impl, _, _)) if varHasUnknownType1(x) =>
        val Some(Name1(lvl, ty2)) = ctx.lookup(x): @unchecked
        unify1(ty2, ty)
        Var1(lvl.toIx(ctx.lvl))

      case (S.Var(x, _), VU1) if varHasUnknownType1(x) =>
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

      case (S.Match(Nil, ps), VPi(x, Expl, t1, t2)) if ps.size > 0 =>
        checkLambdaMatch1(ps.head._2.size, ps, ty) match
          case Left(m) => // postpone
            val placeholder = freshMetaId(ty)
            val pid = newPostponed(PECheck1(ctx, tm, ty, placeholder))
            addBlocking(pid, m)
            debug(
              s"postpone ?p$pid as ?$placeholder: check1 $tm : ${ctx.pretty1(ty)}"
            )
            PostponedCheck1(pid)
          case Right(tm) => tm

      case (S.Pi(DontBind, Expl, t1, t2), VU0(cv)) =>
        unify1(cv, VComp)
        val lev = freshMeta(VLevity)
        val vlev = ctx.eval1(lev)
        val et1 = check1(t1, VU0(VVal(vlev)))
        val fcv = freshCV()
        val vfcv = ctx.eval1(fcv)
        val et2 = check1(t2, VU0(vfcv))
        Fun(lev, et1, fcv, et2)
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

      case (tm, VFlex(m, _)) =>
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

      case S.StringLit(v) =>
        (
          StringLit(v),
          VRigid(
            HPrim(Name("Class")),
            SApp(SId, VLabelLit("java.lang.String"), Expl)
          ),
          VVal(VPrim1(Name("Boxed")))
        )

      case S.Lam(x, i, mty, b) =>
        i match
          case S.ArgNamed(_)   => error(s"implicit lambda in Ty")
          case S.ArgIcit(Impl) => error(s"implicit lambda in Ty")
          case S.ArgIcit(Expl) =>
            val alev = freshMeta(VLevity)
            val acv = Val(alev)
            val avcv = ctx.eval1(acv)
            val ety = tyAnnot(mty, VU0(avcv))
            val cv = freshCV()
            val vcv = ctx.eval1(cv)
            val rt = freshMeta(VU0(vcv))
            val vrt = ctx.eval1(rt)
            val vty = ctx.eval1(ety)
            val eb = check0(b, vrt, vcv)(ctx.bind0(x, ety, vty, acv, avcv))
            (Lam0(x, ety, eb), VFun(ctx.eval1(alev), vty, vcv, vrt), VComp)

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

      case S.IntLit(v) =>
        Infer0(
          IntLit(v),
          VPrim1(Name("Int")),
          VVal(VUnboxed(VPrim1(Name("IntRep"))))
        )
      case S.StringLit(v) => Infer1(LabelLit(v), VPrim1(Name("Label")))

      case S.Var(x @ Name("Label"), _) => Infer1(Prim1(x), VU1)
      case S.Var(x @ Name("Class"), _) =>
        // Label -> Ty (Val Boxed)
        Infer1(
          Prim1(x),
          ctx.eval1(
            Pi(
              DontBind,
              Expl,
              Prim1(Name("Label")),
              U0(Val(Prim1(Name("Boxed"))))
            )
          )
        )

      case S.Var(x @ Name("IO"), _) =>
        // {l : Levity} -> Ty (Val l) -> Ty Comp
        Infer1(
          Prim1(x),
          ctx.eval1(
            Pi(
              DoBind(Name("l")),
              Impl,
              Prim1(Name("Levity")),
              Pi(
                DontBind,
                Expl,
                U0(Val(Var1(mkIx(0)))),
                U0(Comp)
              )
            )
          )
        )
      case S.Var(rIO @ Name("returnIO"), _) =>
        // {l : Levity} {A : Ty (Val l)} -> ^A -> ^(IO {l} A)
        Infer1(
          Prim1(rIO),
          ctx.eval1(
            Pi(
              DoBind(Name("l")),
              Impl,
              Prim1(Name("Levity")),
              Pi(
                DoBind(Name("A")),
                Impl,
                U0(Val(Var1(mkIx(0)))),
                Pi(
                  DontBind,
                  Expl,
                  Lift(
                    Val(Var1(mkIx(1))),
                    Var1(ix0)
                  ),
                  Lift(
                    Comp,
                    App1(
                      App1(Prim1(Name("IO")), Var1(mkIx(2)), Impl),
                      Var1(mkIx(1)),
                      Expl
                    )
                  )
                )
              )
            )
          )
        )
      case S.Var(rRunIO @ Name("unsafePerformIO"), _) =>
        // {l : Levity} {A : Ty (Val l)} -> ^(IO {l} A) -> ^A
        inline def io(ixl: Int, ix: Int) =
          Lift(
            Comp,
            App1(
              App1(Prim1(Name("IO")), Var1(mkIx(ixl)), Impl),
              Var1(mkIx(ix)),
              Expl
            )
          )
        Infer1(
          Prim1(rRunIO),
          ctx.eval1(
            Pi(
              DoBind(Name("l")),
              Impl,
              Prim1(Name("Levity")),
              Pi(
                DoBind(Name("A")),
                Impl,
                U0(Val(Var1(mkIx(0)))),
                Pi(
                  DontBind,
                  Expl,
                  io(1, 0),
                  Lift(
                    Val(Var1(mkIx(2))),
                    Var1(mkIx(1))
                  )
                )
              )
            )
          )
        )
      case S.Var(rIO @ Name("bindIO"), _) =>
        // {l1 l2 : Levity} {A : Ty (Val l1)} {B : Ty (Val l2)} -> ^(IO {l1} A) -> (^A -> ^(IO {l2} B)) -> ^(IO {l2} B)
        inline def io(lix: Int, ix: Int) =
          Lift(
            Comp,
            App1(
              App1(Prim1(Name("IO")), Var1(mkIx(lix)), Impl),
              Var1(mkIx(ix)),
              Expl
            )
          )
        Infer1(
          Prim1(rIO),
          ctx.eval1(
            Pi(
              DoBind(Name("l1")),
              Impl,
              Prim1(Name("Levity")),
              Pi(
                DoBind(Name("l2")),
                Impl,
                Prim1(Name("Levity")),
                Pi(
                  DoBind(Name("A")),
                  Impl,
                  U0(Val(Var1(mkIx(1)))),
                  Pi(
                    DoBind(Name("B")),
                    Impl,
                    U0(Val(Var1(mkIx(1)))),
                    Pi(
                      DontBind,
                      Expl,
                      io(3, 1),
                      Pi(
                        DontBind,
                        Expl,
                        Pi(
                          DontBind,
                          Expl,
                          Lift(
                            Val(Var1(mkIx(4))),
                            Var1(mkIx(2))
                          ),
                          io(4, 2)
                        ),
                        io(4, 2)
                      )
                    )
                  )
                )
              )
            )
          )
        )

      case S.Var(x @ Name("Rep"), _) => Infer1(Prim1(x), VU1)
      case S.Var(x @ Name("ByteRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("ShortRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("IntRep"), _) => Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("LongRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("FloatRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("DoubleRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("CharRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Rep")))
      case S.Var(x @ Name("BoolRep"), _) =>
        Infer1(Prim1(x), VPrim1(Name("BoolRep")))

      case S.Var(x @ Name("Levity"), _) => Infer1(Prim1(x), VU1)
      case S.Var(x @ Name("Boxed"), _) =>
        Infer1(Prim1(x), VPrim1(Name("Levity")))
      case S.Var(x @ Name("Unboxed"), _) =>
        Infer1(
          Prim1(x),
          VPi(
            DontBind,
            Expl,
            VPrim1(Name("Rep")),
            Clos(EEmpty, Prim1(Name("Levity")))
          )
        )

      case S.Var(x @ Name("Val"), _) =>
        Infer1(
          Prim1(x),
          VPi(
            DontBind,
            Expl,
            VPrim1(Name("Levity")),
            Clos(EEmpty, CV1)
          )
        )

      case S.Var(x @ Name("Byte"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("ByteRep"))))))
      case S.Var(x @ Name("Short"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("ShortRep"))))))
      case S.Var(x @ Name("Int"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("IntRep"))))))
      case S.Var(x @ Name("Long"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("LongRep"))))))
      case S.Var(x @ Name("Float"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("FloatRep"))))))
      case S.Var(x @ Name("Double"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("DoubleRep"))))))
      case S.Var(x @ Name("Char"), _) =>
        Infer1(Prim1(x), VU0(VVal(VUnboxed(VPrim1(Name("CharRep"))))))
      case S.Var(x @ Name("Array"), _) =>
        // {l : Levity} -> Ty (Val l) -> Ty (Val Boxed)
        Infer1(
          Prim1(x),
          ctx.eval1(
            Pi(
              DoBind(Name("l")),
              Impl,
              Prim1(Name("Levity")),
              Pi(
                DontBind,
                Expl,
                U0(Val(Var1(mkIx(0)))),
                U0(Val(Prim1(Name("Boxed"))))
              )
            )
          )
        )

      case S.Var(x, _) =>
        ctx.lookup(x) match
          case Some(Name0(x, ty, cv)) =>
            Infer0(Var0(x.toIx(ctx.lvl)), ty, cv)
          case Some(Name1(x, ty)) => Infer1(Var1(x.toIx(ctx.lvl)), ty)
          case None =>
            getGlobal(x) match
              case None => error(s"undefined variable $x")
              case Some(GlobalEntry0(_, _, _, _, _, ty, cv)) =>
                Infer0(Global0(x), ty, cv)
              case Some(GlobalEntry1(_, _, _, _, ty)) =>
                Infer1(Global1(x), ty)
              case Some(GlobalData0(_, _, ps, lev, _)) =>
                val ty = ps.zipWithIndex.foldRight(
                  U0(Val(lev.wk1N(ps.size)))
                ) { case (((icit, x, ty), i), b) =>
                  Pi(x, icit, ty, b)
                }
                debug(ty)
                val vty = ctx.eval1(ctx.quote1(eval1(ty)(EEmpty)))
                Infer1(TCon(x), vty)
              case Some(GlobalCon0(_, dx, cps)) =>
                val GlobalData0(_, _, ps, lev, _) = getGlobalData0(dx)
                val (dargsrev, env) = ps
                  .foldLeft((List.empty[(Ty, Icit)], EEmpty)) {
                    case ((args, env), (i, x, t)) =>
                      val vty = eval1(t)(env)
                      val m = freshMeta(vty)
                      val vm = ctx.eval1(m)
                      ((m, i) :: args, E1(env, vm))
                  }
                val dargs = dargsrev.reverse
                val ts = cps
                  .foldLeft((ctx, List.empty[(Bind, Ty)])) {
                    case ((innerctx, res), (x, lev, t)) =>
                      val qt = innerctx.quote1(eval1(t)(env))
                      val qlev = innerctx.quote1(eval1(lev)(env))
                      val lty = Lift(Val(qlev), qt)
                      (innerctx.insert1(x, lty), (x, lty) :: res)
                  }
                  ._2
                  .reverse
                val tycon = dargs
                  .foldLeft(TCon(dx)) { case (f, (a, i)) => App1(f, a, i) }
                  .wk1N(ts.size)
                val ty =
                  ts.foldRight(Lift(Val(lev.wk1N(ts.size)), tycon)) {
                    case ((x, t), b) =>
                      Pi(x, Expl, t, b)
                  }
                debug(ty)
                val vty = ctx.eval1(ty)
                val lam = ts.zipWithIndex.foldRight(
                  Quote(
                    Con(
                      x,
                      tycon,
                      (0 until cps.size).reverse
                        .map(i => Splice(Var1(mkIx(i))))
                        .toList
                    )
                  )
                ) { case (((x, t), i), b) =>
                  val y = x match
                    case DontBind  => Name(s"x$i")
                    case DoBind(x) => x
                  Lam1(DoBind(y), Expl, t, b)
                }
                debug(lam)
                Infer1(lam, vty)

      case S.Let(x, rec, false, mty, v, b) =>
        val (ety, cv2, vcv2) =
          if rec then (tyAnnot(mty, VU0(VComp)), Comp, VComp)
          else
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(mty, VU0(vcv2))
            (ety, cv2, vcv2)
        val vty = ctx.eval1(ety)
        // if rec then ensureFun(vty, vcv2)
        val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
        val ev = check0(v, vty, vcv2)(if rec then nctx else ctx)
        val (eb, rty, rcv) = infer0(b)(nctx)
        Infer0(
          if rec then LetRec(x, ety, ev, eb)
          else Let0(x, ety, ev, eb),
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
            val lev = freshMeta(VLevity)
            val vlev = ctx.eval1(lev)
            unify1(cv, VVal(vlev))
            val bcv = freshCV()
            val vbcv = ctx.eval1(bcv)
            val eb = check1(b, VU0(vbcv))
            Infer1(Fun(lev, ea, bcv, eb), VU0(VComp))
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
                val (lev, t1, rcv, t2) = ensureFun(fty, fcv)
                val ea = check0(a, t1, VVal(lev))
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

      case S.Hole(_) => error("cannot infer hole")

      case S.Match(Nil, _) =>
        val ty = ctx.eval1(freshMeta(VU1))
        val placeholder = freshMetaId(ty)
        val pid = newPostponed(PECheck1(ctx, tm, ty, placeholder))
        val VFlex(m, _) = ty: @unchecked
        addBlocking(pid, m)
        debug(
          s"postpone ?p$pid as ?$placeholder: check1 $tm : ${ctx.pretty1(ty)}"
        )
        Infer1(PostponedCheck1(pid), ty)

      case S.Match(scruts, ps) =>
        val cv = ctx.eval1(freshCV())
        val ty = ctx.eval1(freshMeta(VU0(cv)))
        val etm = checkMatch(Right(scruts), ps, ty, cv)
        Infer0(etm, ty, cv)

      case S.Foreign(io, ty, code, args) =>
        inline def freshVVal()(implicit ctx: Ctx): Val1 =
          ctx.eval1(Val(freshMeta(VPrim1(Name("Levity")))))
        val vcv = freshVVal()
        val ety = check1(ty, VU0(vcv))
        val ecode = check1(code, VPrim1(Name("Label")))
        val eargs = args.map { t =>
          val cv = freshVVal()
          check0(t, ctx.eval1(freshMeta(VU0(cv))), cv)
        }
        val vt = ctx.eval1(ety)
        val rt =
          if io then VRigid(HPrim(Name("IO")), SApp(SId, vt, Expl)) else vt
        Infer0(Foreign(io, ety, ecode, eargs), rt, if io then VComp else vcv)

      case S.Split(scrut, cs) =>
        val (escrut, ty) = insertPi(infer1(scrut))
        def go(
            t: VTy,
            cs: List[
              (PosInfo, Bind, List[(Bind, S.ArgInfo, Option[S.Tm])], S.Tm)
            ],
            tm: Tm1
        ): Infer =
          if cs.isEmpty then Infer1(tm, t)
          else
            forceAll1(t) match
              case VPi(_, Impl, pt, rt) =>
                val m = freshMeta(pt)
                go(rt(ctx.eval1(m)), cs, App1(tm, m, Impl))
              case VPi(x, _, pt, rt) =>
                cs.indexWhere((_, y, _, _) => x == y) match
                  case -1 => error(s"")
                  case i =>
                    val (pos, _, ps, b) = cs(i)
                    val rem = cs.patch(i, Nil, 1)
                    val lams = ps.foldRight(b) { case ((t, i, ot), b) =>
                      S.Lam(t, i, ot, b)
                    }
                    val elams = check1(lams, pt)(ctx.enter(pos))
                    go(rt(ctx.eval1(elams)), rem, App1(tm, elams, Expl))
              case _ =>
                if cs.nonEmpty then
                  error(s"split case not used")(ctx.enter(cs.head._1))
                Infer1(tm, t)
        go(ty, cs, escrut)

  // elaboration
  def elaborate(d: S.Def): Unit =
    debug(s"elaborate $d")
    d match
      case S.DData(pos, k, dx, psx, cs) =>
        implicit val ctx: Ctx = Ctx.empty(pos)
        if getGlobal(dx).isDefined then error(s"duplicated definition $dx")
        val (innerctx, ps) = psx.foldLeft((ctx, List.empty[(Icit, Bind, Ty)])) {
          case ((ctx, res), (i, x, t)) =>
            val et = check1(t, VU1)(ctx)
            (ctx.bind1(x, et, ctx.eval1(et)), (i, x, et) :: res)
        }
        val lev = k match
          case S.SBoxed => Right(Prim1(Name("Boxed")))
          case S.SUnboxed =>
            if cs.exists(c => c.args.nonEmpty) then
              error(s"unboxed datatype constructors cannot have parameters")
            val lev = cs.size match
              case n if n <= 2 =>
                App1(Prim1(Name("Unboxed")), Prim1(Name("BoolRep")), Expl)
              case n if n <= 128 =>
                App1(Prim1(Name("Unboxed")), Prim1(Name("ByteRep")), Expl)
              case n if n <= 32768 =>
                App1(Prim1(Name("Unboxed")), Prim1(Name("ShortRep")), Expl)
              case _ =>
                App1(Prim1(Name("Unboxed")), Prim1(Name("IntRep")), Expl)
            Right(lev)
          case S.SNewtype =>
            if cs.size != 1 || cs.head.args.size != 1 then
              error(
                s"newtype datatype must have exactly 1 constructor with 1 parameter"
              )
            Left(freshMeta(VLevity))
        setGlobal(
          GlobalData0(
            dx,
            lev.isLeft,
            ps.reverse,
            lev.fold(x => x, x => x),
            cs.map(_.name)
          )
        )
        cs.foreach { case DataCon(pos, cx, cps) =>
          implicit val ctx: Ctx = innerctx
          // TODO: check for simple recursion
          val ecps = cps.map { (x, ty) =>
            val qlev = lev.fold(m => m, _ => freshMeta(VLevity))
            val vlev = ctx.eval1(qlev)
            (x, qlev, check1(ty, VU0(VVal(vlev))))
          }
          setGlobal(GlobalCon0(cx, dx, ecps))
        }
        retryAllPostponed()
        val ums = unsolvedMetas()
        if ums.nonEmpty then
          val str =
            ums.map((id, ty) => s"?$id : ${ctx.pretty1(ty)}").mkString("\n")
          error(s"there are unsolved metas:\n$str")
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
              // if rec then ensureFun(vty, vcv)
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
