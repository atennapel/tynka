package jvmir

import common.Common.{impossible, PrimName}

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TCon(x: GName)

    override def toString: String = this match
      case TCon(x) => s"$x"

    def tdef: TDef = TDef(this)
  export Ty.*

  final case class TDef(ps: Option[List[Ty]], rt: Ty):
    override def toString: String = ps match
      case None => rt.toString
      case _    => s"(${ps.get.mkString(", ")}) -> $rt"
    def head: Ty = ps.get.head
    def tail: TDef = TDef(ps.get.tail, rt)
    def ty: Ty =
      if ps.nonEmpty then impossible()
      else rt
    def drop(n: Int): TDef = TDef(ps.get.drop(n), rt)
    def params: List[Ty] = ps.getOrElse(Nil)
  object TDef:
    def apply(rt: Ty): TDef = TDef(None, rt)
    def apply(t1: Ty, t2: Ty): TDef = TDef(List(t1), t2)
    def apply(t1: Ty, t2: TDef): TDef =
      t2.ps match
        case None     => TDef(List(t1), t2.rt)
        case Some(ps) => TDef(t1 :: ps, t2.rt)
    def apply(ps: List[Ty], t2: Ty): TDef = TDef(Some(ps), t2)
    def apply(ps: List[Ty], t2: TDef): TDef =
      t2.ps match
        case None      => TDef(ps, t2.rt)
        case Some(ps2) => TDef(ps ++ ps2, t2.rt)

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case DDef(
        name: GName,
        gen: Boolean,
        ty: TDef,
        value: Tm
    )
    case DData(
        name: GName,
        cs: List[(GName, List[Ty])]
    )

    override def toString: String = this match
      case DDef(x, _, TDef(None, t), v) => s"def $x : $t = $v"
      case DDef(x, _, t, v) =>
        s"def $x (${t.params.mkString(", ")}) : ${t.rt} = $v"
      case DData(x, Nil) => s"data $x"
      case DData(x, cs) =>
        s"data $x = ${cs
            .map((x, ts) => s"$x${if ts.isEmpty then "" else " "}${ts.mkString(" ")}")
            .mkString(" | ")}"
  export Def.*

  enum Tm:
    case Arg(ix: Int)
    case Var(name: LName)
    case Global(name: GName, ty: Ty)

    case Let(name: LName, ty: Ty, value: Tm, body: Tm)

    case GlobalApp(
        name: GName,
        ty: TDef,
        tc: Boolean,
        as: List[Tm]
    )

    case IntLit(value: Int)

    case Con(name: GName, con: GName, args: List[Tm])

    override def toString: String = this match
      case Arg(i)          => s"'arg$i"
      case Var(x)          => s"'$x"
      case Global(x, _)    => s"$x"
      case Let(x, t, v, b) => s"(let $x : $t = $v; $b)"

      case IntLit(v) => s"$v"

      case GlobalApp(x, _, tc, as) =>
        s"(${if tc then "[tailcall] " else ""}$x ${as.mkString(" ")})"

      case Con(x, cx, Nil) => s"(con $x $cx)"
      case Con(x, cx, as)  => s"(con $x $cx ${as.mkString(" ")})"
  export Tm.*