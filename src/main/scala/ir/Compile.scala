package ir

import common.Common.*
import common.Ref
import core.Globals.*
import core.Evaluation.stage
import Monomorphize.{monomorphize, monomorphizedDatatypes}
import Simplify.simplify
import Syntax.*
import jvmir.Syntax as J

import scala.collection.mutable
import scala.annotation.tailrec

object Compile:
  def compile(top: Name): List[J.Def] =
    val defs = allGlobals.flatMap {
      case GlobalEntry0(x, tm, ty, cv, vv, vty, vcv) =>
        val mty = monomorphize(ty)
        implicit val ref = Ref(0)
        val mtm = monomorphize(stage(tm))
        simplify(x, mtm, mty).map { (x, t, v) =>
          // println(s"def $x : $t = $v")
          implicit val rename: LocalRename = LocalRename()
          v.flattenLams match
            case (None, v) => J.DDef(x, go(t), go(v))
            case (Some(ps, _), v) =>
              ps.zipWithIndex.foreach { case ((x, _), i) =>
                rename.set(x, i, true)
              }
              J.DDef(x, go(t), go(v))
        }
      case _ => Nil
    }
    val dataDefs = monomorphizedDatatypes.map { (dx, cs) =>
      J.DData(dx, cs.map((cx, as) => (cx, as.map((x, t) => (x, go(t))))))
    }
    removeUnused(top, dataDefs ++ defs)

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

  private def removeUnused(top: Name, ds: List[J.Def]): List[J.Def] =
    def isUsed(x: Name, ds: List[J.Def]): Boolean =
      ds.filterNot {
        case J.DDef(y, _, _) => y == x; case _ => false
      }.flatMap(_.globals)
        .contains(x)
    def isDataUsed(x: Name, ds: List[J.Def]): Boolean =
      ds.filterNot { case J.DData(y, _) => y == x; case _ => false }
        .flatMap(_.dataGlobals)
        .contains(x)
    def go(ds: List[J.Def], full: List[J.Def]): Option[List[J.Def]] = ds match
      case Nil => None
      case (d @ J.DData(x, _)) :: tl if isDataUsed(x, full) =>
        go(tl, full).map(d :: _)
      case J.DData(_, _) :: tl => Some(tl)
      case (d @ J.DDef(x, _, _)) :: tl if x == top || isUsed(x, full) =>
        go(tl, full).map(d :: _)
      case J.DDef(x, _, _) :: tl => Some(tl)
    @tailrec
    def loop(ds: List[J.Def]): List[J.Def] = go(ds, ds) match
      case None      => ds
      case Some(nds) => loop(nds)
    loop(ds)

  private def go(t: TDef): J.TDef = t match
    case TDef(Nil, false, rt) => J.TDef(None, go(rt))
    case TDef(Nil, true, rt)  => J.TDef(Some(Nil), go(rt))
    case TDef(ps, _, rt)      => J.TDef(ps.map(go), go(rt))

  private def go(t: Ty): J.Ty = t match
    case TCon(name) => J.TCon(name)

  private def go(t: Tm)(implicit localrename: LocalRename): J.Tm =
    t match
      case Var(x0, _) =>
        val (x, arg) = localrename.get(x0)
        if arg then J.Arg(x) else J.Var(x)
      case Con(cx, _, as)  => J.Con(cx, as.map(go))
      case Field(s, ty, i) => J.Field(go(s), go(ty), i)
      case Global(x, ty)   => J.Global(x, go(ty.ty))

      case Let(x0, t, rt, v, b) =>
        val x = localrename.fresh(x0, false)
        J.Let(x, go(t.ty), go(v), go(b))

      case app @ App(_, _) =>
        val (f, as) = app.flattenApps
        f match
          case Global(x, t) => J.GlobalApp(x, go(t), as.map(go))
          case _            => impossible()

      case Match(s, ty, bty, c, x0, b, o) =>
        val x = localrename.fresh(x0, false)
        J.Match(go(s), go(ty), c, x, go(b), go(o))

      case Join(x0, ps, rty, v, b) =>
        val x = localrename.fresh(x0, false)
        J.Join(
          x,
          ps.map((y, t) => (localrename.fresh(y, false), go(t))),
          go(rty.ty),
          go(v),
          go(b)
        )
      case JoinRec(x0, ps, rty, v, b) =>
        val x = localrename.fresh(x0, false)
        J.JoinRec(
          x,
          ps.map((y, t) => (localrename.fresh(y, false), go(t))),
          go(rty.ty),
          go(v),
          go(b)
        )
      case Jump(x0, ty, args) =>
        val (x, arg) = localrename.get(x0)
        J.Jump(x, args.map(go))

      case ReturnIO(v) => go(v)
      case BindIO(x0, t1, t2, v, b) =>
        val x = localrename.fresh(x0, false)
        J.Let(x, go(t1), go(v), go(b))
      case RunIO(v) => go(v) // TODO: is this correct?

      case Lam(x, ty, bty, b)       => impossible()
      case LetRec(x, ty, bty, v, b) => impossible()
      case Impossible(_)            => impossible()
