package ir

import common.Common.impossible
import common.Ref
import Syntax.*
import jvmir.Syntax as IR

import scala.collection.mutable

/*
 * 1. eta expansion of definitions
 * 2. closure conversion
 * 3. lambda lift
 */
object Compiler:
  def compile(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(go))

  // normalize def name based on jvm limitations
  private def norm(x: GName): GName =
    x
      .replace(".", "$_DOT_$")
      .replace(";", "$_SEMICOLON_$")
      .replace("[", "$_BRACKET_$")
      .replace("/", "$_SLASH_$")
      .replace("<", "$_ANGLELEFT_$")
      .replace(">", "$_ANGLERIGHT_$")
      .replace(":", "$_COLON_$")
      .replace("'", "$_TICK_$")
      .replace("`", "$_BACKTICK_$")
      .replace("@", "$_AT_$")
      .replace("?", "$_QUESTION_$")
      .replace(",", "$_COMMA_$")
      .replace("*", "$_MUL_$")
      .replace("/", "$_DIV_$")
      .replace("%", "$_MOD_$")
      .replace("+", "$_ADD_$")
      .replace("-", "$_SUB_$")
      .replace("=", "$_EQ_$")
      .replace("!", "$_EXCL_$")
      .replace("&", "$_AMPER_$")
      .replace("^", "$_HAT_$")
      .replace("|", "$_PIPE_$")
      .replace("~", "$_TILDE_$")
    // .replace("$", "$_DOLLAR_$") // TODO: fix this

  private def go(d: Def): List[IR.Def] = d match
    case DDef(x, t, v) =>
      val (ps, rt, b) = etaExpand(t, v)
      implicit val name: GName = norm(x)
      implicit val args: Args = ps.zipWithIndex.map { case ((x, _), ix) =>
        x -> ix
      }.toMap
      implicit val newDefs: NewDefs = mutable.ArrayBuffer.empty
      implicit val uniq: Ref[Int] = Ref(0)
      val newdef =
        IR.DDef(name, false, ps.map((_, t) => go(t)), go(t.rt), go(b, true))
      newDefs.toList ++ List(newdef)

  private type Args = Map[Name, Int]
  private type NewDefs = mutable.ArrayBuffer[IR.Def]

  private def go(
      t: Expr,
      tr: Boolean
  )(implicit
      name: GName,
      args: Args,
      defs: NewDefs,
      uniq: Ref[Int]
  ): IR.Tm =
    t match
      case Unit => IR.True
      case Var(x, t) =>
        args.get(x) match
          case Some(ix) => IR.Arg(ix, goTy(t))
          case None     => IR.Local(x.expose, goTy(t))
      case Global(x, t) =>
        if t.ps.nonEmpty then impossible()
        IR.Global(norm(x), false, go(t), Nil)
      case Let(x, TDef(Nil, t), _, v, b) =>
        IR.Let(
          x.expose,
          go(t),
          go(v, false),
          go(b, tr)(name, args - x, defs, uniq)
        )

      case Let(x, t, _, v, b) =>
        val g = lambdaLift(Name(uniq.updateGetOld(_ + 1)), t, v)
        go(b.subst(Map(x -> g)), tr)
      case Lam(x, t1, t2, b) =>
        val g = lambdaLift(Name(uniq.updateGetOld(_ + 1)), TDef(t1, t2), t)
        go(g, tr)

      case Fix(g, x, t1, t2, b, arg) =>
        val glb = fixLift(Name(uniq.updateGetOld(_ + 1)), g, x, t1, t2, b)
        go(App(glb, arg), tr)

      case App(f0, a) =>
        val (f, as) = t.flattenApps
        f match
          case Global(x, t) =>
            if t.ps.size != as.size then impossible()
            IR.Global(
              norm(x),
              if x == name then tr else false,
              go(t),
              as.map(go(_, false))
            )
          case Fix(g, x, t1, t2, b, arg) =>
            val glb = fixLift(Name(uniq.updateGetOld(_ + 1)), g, x, t1, t2, b)
            go(glb.apps(arg :: as), tr)
          case _ => impossible()

      case Pair(t1, t2, fst, snd) =>
        IR.Pair(box(t1, go(fst, false)), box(t2, go(snd, false)))
      case Fst(ty, t) => unbox(ty, IR.Fst(go(t, false)))
      case Snd(ty, t) => unbox(ty, IR.Snd(go(t, false)))

      case BoolLit(true)  => IR.True
      case BoolLit(false) => IR.False

      case IntLit(n)       => IR.IntLit(n)
      case BinOp(op, a, b) => IR.Binop(op, go(a, false), go(b, false))

      case If(TDef(Nil, t), c, a, b) =>
        IR.If(go(t), go(c, false), go(a, tr), go(b, tr))

      case LNil(t) => IR.NilL(go(t))
      case LCons(t, hd, tl) =>
        IR.ConsL(go(t), box(t, go(hd, false)), go(tl, false))

      case CaseList(et, TDef(Nil, t), s, nil, hd, tl, cons) =>
        IR.CaseL(
          go(s, false),
          go(et),
          go(nil, tr),
          hd.expose,
          tl.expose,
          go(cons, tr)(name, args - hd - tl, defs, uniq)
        )

      case Absurd(TDef(Nil, rt)) => IR.Absurd(go(rt))

      case _ => impossible()

  private def box(ty: Ty, tm: IR.Tm): IR.Tm = ty match
    case TPair(_, _) => tm
    case TList(_)    => tm
    case _ =>
      val ct = go(ty)
      tm match
        case IR.Unbox(_, tm) => tm
        case IR.Box(_, tm)   => tm
        case _               => IR.Box(ct, tm)

  private def unbox(ty: Ty, tm: IR.Tm): IR.Tm = ty match
    case TPair(_, _) => tm
    case TList(_)    => tm
    case _ =>
      val ct = go(ty)
      tm match
        case IR.Unbox(_, tm) => tm
        case IR.Box(_, tm)   => tm
        case _               => IR.Unbox(ct, tm)

  private def go(t: Ty): IR.Ty = t match
    case TVoid       => IR.TBool
    case TUnit       => IR.TBool
    case TBool       => IR.TBool
    case TInt        => IR.TInt
    case TPair(_, _) => IR.TPair
    case TList(_)    => IR.TList

  private def go(t: TDef): IR.TDef = t match
    case TDef(ps, rt) => IR.TDef(ps.map(go), go(rt))

  private def goTy(t: TDef): IR.Ty = t match
    case TDef(Nil, rt) => go(rt)
    case _             => impossible()

  private def eta(
      t: TDef,
      ps: List[(Name, Ty)],
      scope: Set[Int] = Set.empty
  ): List[(Name, Ty)] =
    (t, ps) match
      case (TDef(Nil, rt), Nil) => Nil
      case (TDef(t :: ts, rt), Nil) =>
        val y = if scope.isEmpty then 0 else scope.max + 1
        val rest = eta(TDef(ts, rt), Nil, scope + y)
        (Name(y), t) :: rest
      case (TDef(t1 :: ts, rt), (x, t2) :: rest) if t1 == t2 =>
        eta(TDef(ts, rt), rest, scope + x.expose)
      case _ => impossible()

  private def etaExpand(t: TDef, v: Expr): (List[(Name, Ty)], Ty, Expr) =
    val (ps, rt, b) = v.flattenLams
    val mps = eta(t, ps)
    val nps = ps ++ mps
    val nb = b.apps(mps.map((x, t) => Var(x, TDef(t))))
    (nps, t.rt, nb)

  private def lambdaLift(x: Name, t: TDef, v: Expr)(implicit
      name: GName,
      defs: NewDefs
  ): Expr =
    val (ps, rt, d) = etaExpand(t, v)
    val fv = v.fvs
      .map((x, t) => {
        if t.ps.nonEmpty then impossible()
        x -> t.rt
      })
      .distinctBy((y, _) => y)
    val nps = fv ++ ps
    val vv = d.lams(nps, TDef(rt))
    val newname = s"$name$$${x.expose}"
    val args = nps.zipWithIndex.map { case ((x, _), ix) =>
      x -> ix
    }.toMap
    val newdef = IR.DDef(
      newname,
      true,
      nps.map((_, t) => go(t)),
      go(rt),
      go(d, true)(newname, args, defs, Ref(0))
    )
    defs += newdef
    Global(newname, TDef(nps.map(_._2), rt))
      .apps(fv.map((x, t) => Var(x, TDef(t))))

  private def fixLift(x: Name, g: Name, y: Name, t1: Ty, t: TDef, v: Expr)(
      implicit
      name: GName,
      defs: NewDefs
  ): Expr =
    val (ps, rt, d) = etaExpand(t, v)
    val fv = v.fvs
      .filterNot((z, _) => z == g || z == y)
      .map((x, t) => {
        if t.ps.nonEmpty then impossible()
        x -> t.rt
      })
      .distinctBy((y, _) => y)
    val nps = fv ++ List((y, t1)) ++ ps
    val vv = d.lams(nps, TDef(rt))
    val newname = s"$name$$${x.expose}"
    val args = nps.zipWithIndex.map { case ((x, _), ix) =>
      x -> ix
    }.toMap
    val gl = Global(newname, TDef(nps.map(_._2), rt))
      .apps(fv.map((x, t) => Var(x, TDef(t))))
    val d2 = d.subst(Map(g -> gl))
    val newdef = IR.DDef(
      newname,
      true,
      nps.map((_, t) => go(t)),
      go(rt),
      go(d2, true)(newname, args, defs, Ref(0))
    )
    defs += newdef
    gl
