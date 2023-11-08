package ir

import common.Common.*
import common.Ref
import core.Globals.*
import core.Evaluation.stage
import Monomorphize.*
import Simplify.simplify
import Syntax.*
import jvmir.Syntax as J

import scala.collection.mutable
import scala.annotation.tailrec
import jvmir.DataGenerator.dataInfo

object Compile:
  def compile(top: Name): List[J.Def] =
    val defs = allGlobals.flatMap {
      case GlobalEntry0(x, tm, ty, cv, vv, vty, vcv) =>
        val mty = monomorphize(ty)
        implicit val ref = Ref(0)
        val mtm = monomorphize(stage(tm))
        // println(s"def $x : $mty = $mtm")
        simplify(x, mtm, mty).map { (g, x, t, v) =>
          // println(s"def${if g then "[gen]" else ""} $x : $t = $v")
          implicit val rename: LocalRename = LocalRename()
          v.flattenLams match
            case (None, v) => J.DDef(g, x, go(t), go(v))
            case (Some(ps, _), v) =>
              ps.filterNot((_, t) => t == TDummy).zipWithIndex.foreach {
                case ((x, _), i) =>
                  rename.set(x, i, true)
              }
              J.DDef(g, x, go(t), go(v))
        }
      case _ => Nil
    }
    val dataDefs = monomorphizedDatatypes.flatMap {
      case (dx, false, Levity.Boxed, cs) =>
        Some(
          J.DData(dx, cs.map((cx, as) => (cx, as.map((x, t) => (x, go(t))))))
        )
      case _ => None
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
        case J.DDef(_, y, _, _) => y == x; case _ => false
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
      case (d @ J.DDef(_, x, _, _)) :: tl if x == top || isUsed(x, full) =>
        go(tl, full).map(d :: _)
      case J.DDef(_, x, _, _) :: tl => Some(tl)
    @tailrec
    def loop(ds: List[J.Def]): List[J.Def] = go(ds, ds) match
      case None      => ds
      case Some(nds) => loop(nds)
    loop(ds)

  private def go(t: TDef): J.TDef = t match
    case TDef(Nil, rt) => J.TDef(None, go(rt))
    case TDef(ps, rt)  => J.TDef(ps.filterNot(_ == TDummy).map(go), go(rt))

  private def go(t: Ty): J.Ty = t match
    case TPrim(Name("Byte"))   => J.TByte
    case TPrim(Name("Short"))  => J.TShort
    case TPrim(Name("Int"))    => J.TInt
    case TPrim(Name("Long"))   => J.TLong
    case TPrim(Name("Float"))  => J.TFloat
    case TPrim(Name("Double")) => J.TDouble
    case TPrim(Name("Char"))   => J.TChar
    case TArray(ty)            => J.TArray(go(ty))
    case TClass(x)             => J.TClass(x)
    case TCon(dx) =>
      val info = monomorphizedDatatype(dx)
      info._3 match
        case Levity.Boxed       => J.TCon(dx)
        case Unboxed(ByteRep)   => J.TByte
        case Unboxed(ShortRep)  => J.TShort
        case Unboxed(IntRep)    => J.TInt
        case Unboxed(LongRep)   => J.TLong
        case Unboxed(FloatRep)  => J.TFloat
        case Unboxed(DoubleRep) => J.TDouble
        case Unboxed(CharRep)   => J.TChar
        case Unboxed(BoolRep)   => J.TBool
    case _ => impossible()

  private def go(t: Tm)(implicit localrename: LocalRename): J.Tm =
    t match
      case Var(x0, _) =>
        val (x, arg) = localrename.get(x0)
        if arg then J.Arg(x) else J.Var(x)
      case Global(x, TDef(Nil, ty)) => J.Global(x, go(ty))
      case Global(x, _)             => impossible()

      case IntLit(v)    => J.IntLit(v)
      case StringLit(v) => J.StringLit(v)

      case Let(_, x0, TDef(Nil, TDummy), rt, v, b) => go(b)
      case l @ Let(_, x0, t, rt, v, b) =>
        val x = localrename.fresh(x0, false)
        J.Let(x, go(t.ty), go(v), go(b))

      case app @ App(_, _) =>
        val (f, as) = app.flattenApps
        f match
          case Global(x, t) =>
            val ps = as.zip(t.ps).filterNot((_, t) => t == TDummy)
            J.GlobalApp(x, go(t), ps.map(_._1).map(go))
          case _ => impossible()

      case Con(dx, cx, as) =>
        val info = monomorphizedDatatype(dx)
        if info._2 then go(as.head)
        else
          info._3 match
            case Levity.Boxed => J.Con(cx, as.map(go))
            case Unboxed(_) =>
              J.IntLit(info._4.indexWhere((cx2, _) => cx == cx2))

      case Field(dx, cx, s, ty, i) =>
        val info = monomorphizedDatatype(dx)
        if info._2 then go(s)
        else
          info._3 match
            case Levity.Boxed => J.Field(cx, go(s), i)
            case Unboxed(_)   => impossible()

      case Match(dx, s, bty, c, x0, b, o) =>
        val info = monomorphizedDatatype(dx)
        if info._2 then go(b.subst(x0, s))
        else
          info._3 match
            case Levity.Boxed =>
              val x = localrename.fresh(x0, false)
              o match
                case Impossible(_) => J.Match(go(s), c, x, go(b), None)
                case _             => J.Match(go(s), c, x, go(b), Some(go(o)))
            case Unboxed(_) =>
              val ix = info._4.indexWhere((cx2, _) => c == cx2)
              o match
                case Impossible(_) => J.FinMatch(go(s), ix, go(b), None)
                case _             => J.FinMatch(go(s), ix, go(b), Some(go(o)))

      case Join(_, _, TDummy, _, b) => go(b)
      case Join(x0, ps0, rty, v, b) =>
        val x = localrename.fresh(x0, false)
        val ps = ps0.filterNot((_, t) => t == TDummy)
        J.Join(
          x,
          ps.map((y, t) => (localrename.fresh(y, false), go(t))),
          go(v),
          go(b)
        )
      case JoinRec(_, _, TDummy, _, b) => go(b)
      case JoinRec(x0, ps0, rty, v, b) =>
        val x = localrename.fresh(x0, false)
        val ps = ps0.filterNot((_, t) => t == TDummy)
        J.JoinRec(
          x,
          ps.map((y, t) => (localrename.fresh(y, false), go(t))),
          go(v),
          go(b)
        )
      case Jump(x0, ty, args) =>
        val (x, arg) = localrename.get(x0)
        val ps = args.zip(ty.ps).filterNot((_, t) => t == TDummy)
        J.Jump(x, ps.map(_._1).map(go))

      case Foreign(ty, code, args) =>
        J.Foreign(go(ty), code, args.map((t, ty) => (go(t), go(ty))))

      case Lam(ps, bty, b)          => impossible()
      case LetRec(x, ty, bty, v, b) => impossible()
      case Impossible(_)            => impossible()
      case DummyValue               => impossible()
