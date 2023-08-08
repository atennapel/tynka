package ir

import common.Common.impossible
import common.Ref
import Syntax.*
import jvmir.Syntax as J

import scala.collection.mutable
import scala.annotation.tailrec

object Compilation:
  def compile(ds: Defs): J.Defs =
    val jds = ds.toList.flatMap(go)
    J.Defs(removeUnused(jds))

  private def removeUnused(ds: List[J.Def]): List[J.Def] =
    def isUsed(x: J.GName, ds: List[J.Def]): Boolean =
      ds.filterNot { case J.DDef(y, _, _, _) => y == x; case _ => false }
        .flatMap(_.globals)
        .contains(x)
    def isDataUsed(x: J.GName, ds: List[J.Def]): Boolean =
      ds.filterNot { case J.DData(y, _) => y == x; case _ => false }
        .flatMap(_.dataGlobals)
        .contains(x)
    def go(ds: List[J.Def], full: List[J.Def]): Option[List[J.Def]] = ds match
      case Nil => None
      case (d @ J.DData(x, _)) :: tl if isDataUsed(x, full) =>
        go(tl, full).map(d :: _)
      case J.DData(_, _) :: tl => Some(tl)
      case (d @ J.DDef(x, _, _, _)) :: tl if x == "main" || isUsed(x, full) =>
        go(tl, full).map(d :: _)
      case J.DDef(x, _, _, _) :: tl => Some(tl)
    @tailrec
    def loop(ds: List[J.Def]): List[J.Def] = go(ds, ds) match
      case None      => ds
      case Some(nds) => loop(nds)
    loop(ds)

  private type LocalMap = mutable.Map[LName, (LName, Boolean)]
  private case class LocalRename(
      ref: Ref[LName] = Ref(0),
      map: LocalMap = mutable.Map.empty
  ):
    def get(oldName: LName): (LName, Boolean) = map(oldName)
    def set(oldName: LName, newName: LName, isArg: Boolean): Unit =
      map += oldName -> (newName, isArg)
    def fresh(oldName: LName, isArg: Boolean): LName =
      val x = ref.updateGetOld(_ + 1)
      map += oldName -> (x, isArg)
      x

  private def go(d: Def): List[J.Def] =
    conv(d).map {
      case DDef(x, gen, t, v) =>
        implicit val defname: GName = x
        implicit val rename: LocalRename = LocalRename()
        v.flattenLams match
          case (None, v) => J.DDef(x, gen, go(t), go(v, true))
          case (Some((ps, bt)), v) =>
            ps.zipWithIndex.foreach { case ((x, _), i) =>
              rename.set(x, i, true)
            }
            J.DDef(x, gen, go(t), go(v, true))
      case DData(x, cs) => J.DData(x, cs.map((cx, as) => (cx, as.map(go))))
    }

  private def go(t: Tm, tr: Boolean)(implicit
      defname: GName,
      localrename: LocalRename
  ): J.Tm =
    t match
      case Var(x0, _) =>
        val (x, arg) = localrename.get(x0)
        if arg then J.Arg(x) else J.Var(x)
      case Global(x, t) =>
        t match
          case TDef(Nil, false, rt) => J.Global(x, go(t.rt))
          case ty => J.GlobalApp(x, go(ty), tr && x == defname, List())

      case IntLit(n)    => J.IntLit(n)
      case BoolLit(b)   => J.BoolLit(b)
      case StringLit(v) => J.StringLit(v)

      case app @ App(_, _) =>
        val (f, as) = app.flattenApps
        f match
          case Global(x, t) =>
            J.GlobalApp(
              x,
              go(t),
              tr && x == defname,
              as.map(go(_, false))
            )
          case _ => impossible()

      case Let(x0, t, rt, v, b) =>
        val x = localrename.fresh(x0, false)
        J.Let(x, go(t.ty), go(v, false), go(b, tr))

      case Con(x, cx, as)       => J.Con(x, cx, as.map(go(_, false)))
      case Field(dty, cx, s, i) => J.Field(dty, cx, go(s, false), i)

      case Match(dty, rty, x0, scrut, cs, other) =>
        val x = localrename.fresh(x0, false)
        J.Match(
          dty,
          go(rty.rt),
          x,
          go(scrut, false),
          cs.map((x, t) => (x, go(t, tr))),
          other.map(go(_, tr))
        )

      case ReturnIO(v) => go(v, tr)
      case BindIO(t1, t2, x0, v, b) =>
        val x = localrename.fresh(x0, false)
        J.Let(x, go(t1), go(v, false), go(b, tr))
      case RunIO(v) => go(v, tr)

      case Foreign(_, rt, cmd, args) =>
        J.Foreign(go(rt), cmd, args.map((t, ty) => (go(t, false), go(ty))))

      case Lam(_, _, _, _)       => impossible()
      case Fix(_, _, _, _, _, _) => impossible()

  private def go(t: Ty): J.Ty = t match
    case TCon(x)        => J.TCon(x)
    case TConCon(x, cx) => J.TConCon(x, cx)
    case TForeign(x)    => J.TForeign(x)
    case TArray(ty)     => J.TArray(go(ty))

  private def go(t: TDef): J.TDef = t match
    case TDef(Nil, false, rt) => J.TDef(None, go(rt))
    case TDef(Nil, true, rt)  => J.TDef(Some(Nil), go(rt))
    case TDef(ps, _, rt)      => J.TDef(ps.map(go), go(rt))

  private def goTy(t: TDef): J.Ty = t match
    case TDef(Nil, false, rt) => go(rt)
    case _                    => impossible()

  // simplify and lambdalift
  private type NewDefs = mutable.ArrayBuffer[Def]

  private case class GlobalGen(ref: Ref[Int] = Ref(0)):
    def gen()(implicit defname: GName): GName =
      s"$defname$$${ref.updateGetOld(_ + 1)}"

  private case class LocalGen(ref: Ref[LName] = Ref(0)):
    def fresh(): LName = ref.updateGetOld(_ + 1)
  private object LocalGen:
    def apply(l: LName): LocalGen = LocalGen(Ref(l))

  private def conv(d: Def): List[Def] = d match
    case DDef(x, gen, t, v) =>
      val (ps, rt, b) = etaExpand(t, v)
      implicit val defname: GName = x
      implicit val newDefs: NewDefs = mutable.ArrayBuffer.empty
      implicit val globalgen: GlobalGen = GlobalGen()
      implicit val localgen: LocalGen = LocalGen(v.maxName + 1)
      val cb = conv(b).lams(ps, TDef(rt))
      newDefs.toList ++ List(DDef(x, gen, t, cb))
    case d @ DData(_, _) => List(d)

  private def conv(
      tm: Tm
  )(implicit
      defs: NewDefs,
      globalgen: GlobalGen,
      localgen: LocalGen,
      defname: GName
  ): Tm =
    tm match
      case Var(x, t)    => tm
      case Global(x, t) => tm
      case IntLit(n)    => tm
      case BoolLit(n)   => tm
      case StringLit(v) => tm

      case Con(x, cx, as)   => Con(x, cx, as.map(conv))
      case Lam(x, t, rt, b) => Lam(x, t, rt, conv(b))

      case Field(dty, cx, s, i) =>
        conv(s) match
          case Con(name, con, as) => as(i)
          case cs                 => Field(dty, cx, cs, i)

      case App(f, a) =>
        conv(f) match
          case Lam(x, t, rt, b)    => conv(Let(x, TDef(t), rt, a, b))
          case Let(x, t, rt, v, b) => conv(Let(x, t, rt.tail, v, App(b, a)))
          case f                   => App(f, conv(a))

      case Let(x, t, bt, v, b) =>
        conv(v) match
          case Let(y, t2, bt2, v2, b2) =>
            conv(Let(y, t2, bt, v2, Let(x, t, bt, b2, b)))
          case v =>
            val c = b.fvs.count((y, _) => x == y)
            if c == 0 then conv(b)
            else if c == 1 || isSmall(v) then conv(b.subst(Map(x -> v)))
            else if !t.io && t.ps.isEmpty then
              val (vs, spine) = eta(bt.params)
              Let(x, t, TDef(bt.io, bt.rt), v, conv(b.apps(spine)))
                .lams(vs, TDef(bt.io, bt.rt))
            else
              val (vs, spine) = eta(t.params)
              val fv = v.fvs.map((x, t) => (x, t.ty)).distinctBy((y, _) => y)
              val nps = fv ++ vs
              val args = nps.zipWithIndex.map { case ((x, _), ix) =>
                x -> ix
              }.toMap
              val gx = globalgen.gen()
              defs += DDef(
                gx,
                true,
                TDef(fv.map(_._2), t),
                conv(v.apps(spine).lams(nps, TDef(t.io, t.rt)))
              )
              val gl = Global(gx, TDef(nps.map(_._2), t.io, t.rt))
                .apps(fv.map((x, t) => Var(x, TDef(t))))
              val (vs2, spine2) = eta(bt.params)
              conv(
                b.subst(Map(x -> gl)).apps(spine2).lams(vs2, TDef(bt.io, bt.rt))
              )

      case Fix(t1, t2, g, x, b0, arg) =>
        val (vs, spine) = eta(t2.params)
        val fv = b0.fvs
          .filterNot((y, _) => y == g || y == x)
          .map((x, t) => (x, t.ty))
          .distinctBy((y, _) => y)
        val nps = fv ++ List((x, t1)) ++ vs
        val args = nps.zipWithIndex.map { case ((x, _), ix) =>
          x -> ix
        }.toMap
        val gx = globalgen.gen()
        val gl = Global(gx, TDef(nps.map(_._2), t2.io, t2.rt))
          .apps(fv.map((x, t) => Var(x, TDef(t))))
        val b = conv(
          b0.subst(Map(g -> gl)).apps(spine).lams(nps, TDef(t2.io, t2.rt))
        )
        defs += DDef(
          gx,
          true,
          TDef(fv.map(_._2) ++ List(t1), t2),
          b
        )
        App(gl, conv(arg))

      case Match(dty, rty, mx, scrut, cs, other) =>
        conv(scrut) match
          case v @ BoolLit(b) =>
            cs.toMap.get(if b then "True" else "False") match
              case Some(b) => conv(b.subst(Map(mx -> v)))
              case None    => impossible()
          case v @ Con(_, x, as) =>
            cs.toMap.get(x) match
              case Some(b) => conv(b.subst(Map(mx -> v)))
              case None    => conv(other.get)
          case v @ cscrut =>
            val (vs, spine) = eta(rty.params)
            Match(
              dty,
              TDef(rty.io, rty.rt),
              mx,
              cscrut,
              cs.map((x, t) => (x, conv(t.apps(spine)))),
              other.map(t => conv(t.apps(spine)))
            ).lams(vs, TDef(rty.io, rty.rt))

      case ReturnIO(v) => ReturnIO(conv(v))
      case BindIO(t1, t2, x, v, b) =>
        conv(v) match
          case BindIO(t3, t4, y, v2, b2) =>
            conv(BindIO(t3, t2, y, v2, BindIO(t4, t2, x, b2, b)))
          case ReturnIO(v) => conv(b.subst(Map(x -> v)))
          case v           => BindIO(t1, t2, x, v, conv(b))
      case RunIO(c) =>
        conv(c) match
          case ReturnIO(v) => v
          case c           => RunIO(c)

      case Foreign(io, rt, l, as) =>
        (l, as.map((a, _) => conv(a))) match
          // +
          case ("op:96", List(IntLit(a), IntLit(b))) => IntLit(a + b)
          case ("op:96", List(a, IntLit(0)))         => a
          case ("op:96", List(IntLit(0), b))         => b
          // -
          case ("op:100", List(IntLit(a), IntLit(b))) => IntLit(a - b)
          case ("op:100", List(IntLit(0), b)) =>
            conv(Foreign(io, rt, "op:116", List((b, as(1)._2))))
          case ("op:100", List(a, IntLit(0))) => a
          // *
          case ("op:104", List(_, IntLit(0)))         => IntLit(0)
          case ("op:104", List(IntLit(0), _))         => IntLit(0)
          case ("op:104", List(a, IntLit(1)))         => a
          case ("op:104", List(IntLit(1), a))         => a
          case ("op:104", List(IntLit(a), IntLit(b))) => IntLit(a * b)
          // /
          case ("op:108", List(IntLit(a), IntLit(b))) => IntLit(a / b)
          case ("op:108", List(a, IntLit(1)))         => a
          // %
          case ("op:112", List(IntLit(a), IntLit(b))) => IntLit(a % b)
          case ("op:112", List(a, IntLit(1)))         => IntLit(0)
          // neg
          case ("op:116", List(IntLit(a))) => IntLit(-a)
          // ==
          case ("branch:153", List(IntLit(a), IntLit(b))) =>
            BoolLit(a == b)
          // !=
          case ("branch:154", List(IntLit(a), IntLit(b))) =>
            BoolLit(a != b)
          // <
          case ("branch:155", List(IntLit(a), IntLit(b))) =>
            BoolLit(a < b)
          // >
          case ("branch:157", List(IntLit(a), IntLit(b))) =>
            BoolLit(a > b)
          // <=
          case ("branch:158", List(IntLit(a), IntLit(b))) =>
            BoolLit(a <= b)
          // >=
          case ("branch:156", List(IntLit(a), IntLit(b))) =>
            BoolLit(a >= b)

          case (
                "invokeVirtual:java.lang.String.concat",
                List(StringLit(""), b)
              ) =>
            b
          case (
                "invokeVirtual:java.lang.String.concat",
                List(a, StringLit(""))
              ) =>
            a
          case (
                "invokeVirtual:java.lang.String.concat",
                List(StringLit(a), StringLit(b))
              ) =>
            StringLit(a + b)

          case (l, gas) => Foreign(io, rt, l, gas.zip(as.map(_._2)))

  private def isSmall(v: Tm): Boolean = v match
    case Var(_, _)      => true
    case Global(_, _)   => true
    case IntLit(_)      => true
    case BoolLit(_)     => true
    case StringLit(_)   => true
    case Con(_, _, Nil) => true
    case _              => false

  private def etaExpand(t: TDef, v: Tm): (List[(LName, Ty)], Ty, Tm) =
    val (ps, b) = v.flattenLams
    val ps1 = ps.map((ps, _) => ps).getOrElse(Nil)
    val mps = eta(t, ps1, v.usedNames)
    val nps = ps1 ++ mps
    val nb = b.apps(mps.map((x, t) => Var(x, TDef(t))))
    (nps, t.rt, nb)

  private def eta(
      t: TDef,
      ps: List[(LName, Ty)],
      scope: Set[LName] = Set.empty
  ): List[(LName, Ty)] =
    (t, ps) match
      case (TDef(Nil, _, rt), Nil) => Nil
      case (TDef(t :: ts, io, rt), Nil) =>
        val y = if scope.isEmpty then 0 else scope.max + 1
        val rest = eta(TDef(ts, io, rt), Nil, scope + y)
        (y, t) :: rest
      case (TDef(t1 :: ts, io, rt), (x, t2) :: rest) if t1 == t2 =>
        eta(TDef(ts, io, rt), rest, scope + x)
      case _ => impossible()

  private def eta(ps: List[Ty])(implicit
      localgen: LocalGen
  ): (List[(LName, Ty)], List[Tm]) =
    val vs =
      ps.foldLeft[List[(LName, Ty)]](Nil) { case (vs, ty) =>
        vs ++ List((localgen.fresh(), ty))
      }
    val spine = vs.map((x, t) => Var(x, TDef(t)))
    (vs, spine)
