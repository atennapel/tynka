package ir

import common.Common.*

object Syntax:
  type LName = Int

  enum Ty:
    case TCon(name: Name)

    override def toString: String = this match
      case TCon(name) => s"$name"

    def dataGlobals: Set[Name] = this match
      case TCon(x) => Set(x)
  export Ty.*

  final case class TDef(ps: List[Ty], io: Boolean, rt: Ty):
    override def toString: String = ps match
      case Nil if !io => s"$rt"
      case ps =>
        s"${ps.mkString("(", ", ", ")")} ->${if io then " IO" else ""} $rt"
    def tail: TDef = TDef(ps.tail, io, rt)
    def ty: Ty = ps match
      case Nil if !io => rt
      case _          => impossible()
    def head: Ty = ps.head
    def returnType = TDef(Nil, io, rt)
    def isFunction: Boolean = ps.nonEmpty && !io
    def dataGlobals: Set[Name] =
      ps.flatMap(_.dataGlobals).toSet ++ rt.dataGlobals
    def drop(n: Int): TDef = TDef(ps.drop(n), io, rt)
    def returnIO: TDef = if io then impossible() else TDef(ps, true, rt)
    def runIO: TDef = if !io then impossible() else TDef(ps, false, rt)
  object TDef:
    def apply(rt: Ty): TDef = TDef(Nil, false, rt)
    def apply(io: Boolean, rt: Ty): TDef = TDef(Nil, io, rt)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.io, rt.rt)
    def apply(ts: List[Ty], t: TDef): TDef = TDef(ts ++ t.ps, t.io, t.rt)

  enum Tm:
    case Var(name: LName, ty: TDef)
    case Global(name: Name, ty: TDef)
    case Let(name: LName, ty: TDef, bty: TDef, value: Tm, body: Tm)
    case LetRec(name: LName, ty: TDef, bty: TDef, value: Tm, body: Tm)
    case Join(
        name: LName,
        ps: List[(LName, Ty)],
        rty: TDef,
        value: Tm,
        body: Tm
    )
    case JoinRec(
        name: LName,
        ps: List[(LName, Ty)],
        rty: TDef,
        value: Tm,
        body: Tm
    )
    case Jump(name: LName, ty: TDef, args: List[Tm])
    case Lam(name: LName, ty: Ty, bty: TDef, body: Tm)
    case App(fn: Tm, arg: Tm)
    case Con(name: Name, ty: Ty, args: List[Tm])
    case Match(
        scrut: Tm,
        ty: Ty,
        bty: TDef,
        con: Name,
        name: LName,
        body: Tm,
        other: Tm
    )
    case Impossible(ty: TDef)
    case Field(value: Tm, rt: Ty, ix: Int)
    case ReturnIO(value: Tm)
    case BindIO(x: LName, t1: Ty, t2: Ty, value: Tm, body: Tm)
    case RunIO(value: Tm)

    override def toString: String = this match
      case Var(x, _)              => s"'$x"
      case Global(x, _)           => s"$x"
      case Let(x, ty, _, v, b)    => s"(let '$x : $ty = $v; $b)"
      case LetRec(x, ty, _, v, b) => s"(let rec '$x : $ty = $v; $b)"
      case Join(x, ps, ty, v, b) =>
        val sps = ps match
          case Nil => ""
          case ps  => s" ${ps.map((x, t) => s"($x : $t)").mkString(" ")}"
        s"(join '$x$sps : ${ty} = $v; $b)"
      case JoinRec(x, ps, ty, v, b) =>
        val sps = ps match
          case Nil => ""
          case ps  => s" ${ps.map((x, t) => s"($x : $t)").mkString(" ")}"
        s"(join rec '$x$sps : ${ty} = $v; $b)"
      case Jump(x, _, Nil)  => s"(jump $x)"
      case Jump(x, _, args) => s"(jump $x ${args.mkString(" ")})"
      case Lam(x, ty, _, b) => s"(\\('$x : $ty) => $b)"
      case App(fn, arg)     => s"($fn $arg)"
      case Con(x, _, Nil)   => s"$x"
      case Con(x, _, as)    => s"($x ${as.mkString(" ")})"
      case Match(scrut, _, _, c, x, b, e) =>
        s"(match $scrut | $c as '$x => $b | _ => $e)"
      case Impossible(_)         => "impossible"
      case Field(value, _, ix)   => s"(#$ix $value)"
      case ReturnIO(v)           => s"(returnIO $v)"
      case BindIO(x, _, _, v, b) => s"($x <- $v; $b)"
      case RunIO(v)              => s"(unsafePerformIO $v)"

    def apps(args: List[Tm]) = args.foldLeft(this)(App.apply)

    def lams(ps: List[(LName, Ty)], rt: TDef): Tm =
      ps.foldRight[(Tm, TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (Lam(x, t, rt, b), TDef(t, rt))
      }._1

    def flattenApps: (Tm, List[Tm]) = this match
      case App(fn, arg) =>
        val (f, args) = fn.flattenApps
        (f, args ++ List(arg))
      case t => (t, Nil)

    def flattenLams: (Option[(List[(LName, Ty)], TDef)], Tm) =
      def go(t: Tm): (Option[(List[(LName, Ty)], TDef)], Tm) = t match
        case Lam(x, t1, t2, b) =>
          val (opt, b2) = go(b)
          opt match
            case None => (Some((List((x, t1)), t2)), b2)
            case Some((xs, rt)) =>
              (Some(((x, t1) :: xs, rt)), b2)
        case b => (None, b)
      go(this)

    def subst(x: LName, v: Tm): Tm = subst(Map(x -> v))
    def subst(ss: Map[LName, Tm]): Tm =
      inline def go(t: Tm) = t.subst(ss)
      this match
        case Var(x, _)             => ss.get(x).getOrElse(this)
        case Global(x, _)          => this
        case Impossible(_)         => this
        case Field(value, ty, ix)  => Field(go(value), ty, ix)
        case App(fn, arg)          => App(go(fn), go(arg))
        case Con(x, t, args)       => Con(x, t, args.map(go(_)))
        case Let(x, ty, bty, v, b) => Let(x, ty, bty, go(v), go(b))
        case LetRec(x, ty, bty, v, b) =>
          LetRec(x, ty, bty, go(v), go(b))
        case Join(x, ps, ty, v, b) => Join(x, ps, ty, go(v), go(b))
        case JoinRec(x, ps, ty, v, b) =>
          JoinRec(x, ps, ty, go(v), go(b))
        case Jump(x, t, args) =>
          val args2 = args.map(go(_))
          ss.get(x).map(hd => hd.apps(args2)).getOrElse(Jump(x, t, args2))
        case Lam(x, ty, bty, body) => Lam(x, ty, bty, go(body))
        case Match(s, t, bty, c, x, b, o) =>
          Match(go(s), t, bty, c, x, go(b), go(o))
        case ReturnIO(v) => ReturnIO(go(v))
        case BindIO(x, t1, t2, v, b) =>
          BindIO(x, t1, t2, go(v), go(b))
        case RunIO(v) => RunIO(go(v))

    def free: List[(LName, TDef)] = this match
      case Var(x, t)           => List((x, t))
      case Global(x, _)        => Nil
      case Con(_, _, args)     => args.flatMap(_.free)
      case App(f, a)           => f.free ++ a.free
      case Impossible(_)       => Nil
      case Field(v, _, ix)     => v.free
      case Let(x, ty, _, v, b) => v.free ++ b.free.filterNot((y, _) => x == y)
      case LetRec(x, ty, _, v, b) =>
        v.free.filterNot((y, _) => x == y) ++ b.free.filterNot((y, _) => x == y)
      case Join(x, ps, ty, v, b) => v.free ++ b.free.filterNot((y, _) => x == y)
      case JoinRec(x, ps, ty, v, b) =>
        v.free.filterNot((y, _) => x == y) ++ b.free.filterNot((y, _) => x == y)
      case Jump(x, t, args) => List((x, t)) ++ args.flatMap(_.free)
      case Lam(x, ty, _, b) => b.free.filterNot((y, _) => x == y)
      case Match(s, _, _, _, x, b, o) =>
        s.free ++ b.free.filterNot((y, _) => x == y) ++ o.free
      case ReturnIO(v)           => v.free
      case BindIO(x, _, _, v, b) => v.free ++ b.free.filterNot((y, _) => x == y)
      case RunIO(v)              => v.free
  export Tm.*
