package ir

import common.Common.impossible
import common.Ref
import Syntax.*
import jvmir.Syntax as J

import scala.collection.mutable

object Compilation:
  def compile(ds: Defs): J.Defs = J.Defs(ds.toList.flatMap(go))

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
        if t.ps.nonEmpty then impossible()
        J.Global(x, go(t.rt))

      case IntLit(n) => J.IntLit(n)

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

      case Con(x, cx, as) => J.Con(x, cx, as.map(go(_, false)))
      case Field(s, i)    => J.Field(go(s, false), i)

      case Match(dty, rty, scrut, cs, other) =>
        J.Match(
          dty,
          go(rty.ty),
          go(scrut, false),
          cs.map((x, t) => (x, go(t, tr))),
          other.map(go(_, tr))
        )

      case Lam(_, _, _, _)       => impossible()
      case Fix(_, _, _, _, _, _) => impossible()

  private def go(t: Ty): J.Ty = t match
    case TCon(x) => J.TCon(x)

  private def go(t: TDef): J.TDef = t match
    case TDef(Nil, rt) => J.TDef(None, go(rt))
    case TDef(ps, rt)  => J.TDef(ps.map(go), go(rt))

  private def goTy(t: TDef): J.Ty = t match
    case TDef(Nil, rt) => go(rt)
    case _             => impossible()

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
  ): Tm = tm match
    case Var(x, t)    => tm
    case Global(x, t) => tm
    case IntLit(n)    => tm

    case Con(x, cx, as)   => Con(x, cx, as.map(conv))
    case Lam(x, t, rt, b) => Lam(x, t, rt, conv(b))

    case Field(s, i) =>
      conv(s) match
        case Con(name, con, as) => as(i)
        case cs                 => Field(cs, i)

    case App(f, a) =>
      conv(f) match
        case Lam(x, t, rt, b)    => conv(Let(x, TDef(t), rt, a, b))
        case Let(x, t, rt, v, b) => conv(Let(x, t, rt.tail, v, App(b, a)))
        case f                   => App(f, conv(a))

    case Let(x, t, bt, v, b0) =>
      conv(v) match
        case Let(y, t2, bt2, v2, b2) =>
          conv(Let(y, t2, bt, v2, Let(x, t, bt, b2, b0)))
        case v =>
          val b = conv(b0)
          val c = b.fvs.count((y, _) => x == y)
          if c == 0 then b
          else if c == 1 || isSmall(v) then conv(b.subst(Map(x -> v)))
          else if t.ps.isEmpty then
            val (vs, spine) = eta(bt.params)
            Let(x, t, TDef(bt.rt), v, conv(b.apps(spine)))
              .lams(vs, TDef(bt.rt))
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
              conv(v.apps(spine).lams(nps, TDef(t.rt)))
            )
            val gl = Global(gx, TDef(nps.map(_._2), t.rt))
              .apps(fv.map((x, t) => Var(x, TDef(t))))
            val (vs2, spine2) = eta(bt.params)
            conv(b.subst(Map(x -> gl)).apps(spine2).lams(vs2, TDef(bt.rt)))

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
      val gl = Global(gx, TDef(nps.map(_._2), t2.rt))
        .apps(fv.map((x, t) => Var(x, TDef(t))))
      val b = conv(
        b0.apps(spine).lams(nps, TDef(t2.rt)).subst(Map(g -> gl))
      )
      defs += DDef(
        gx,
        true,
        TDef(fv.map(_._2) ++ List(t1), t2),
        b
      )
      App(gl, conv(arg))

    case Match(dty, rty, scrut, cs, other) =>
      conv(scrut) match
        case Con(_, x, as) =>
          cs.toMap.get(x) match
            case Some(b) => conv(b)
            case None    => conv(other.get)
        case cscrut =>
          val (vs, spine) = eta(rty.params)
          val res = Match(
            dty,
            TDef(rty.rt),
            cscrut,
            cs.map((x, t) => (x, conv(t.apps(spine)))),
            other.map(t => conv(t.apps(spine)))
          ).lams(vs, TDef(rty.rt))
          res

  private def isSmall(v: Tm): Boolean = v match
    case Var(_, _)      => true
    case Global(_, _)   => true
    case IntLit(_)      => true
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
      case (TDef(Nil, rt), Nil) => Nil
      case (TDef(t :: ts, rt), Nil) =>
        val y = if scope.isEmpty then 0 else scope.max + 1
        val rest = eta(TDef(ts, rt), Nil, scope + y)
        (y, t) :: rest
      case (TDef(t1 :: ts, rt), (x, t2) :: rest) if t1 == t2 =>
        eta(TDef(ts, rt), rest, scope + x)
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
