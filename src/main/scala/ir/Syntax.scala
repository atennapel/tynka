package ir

import common.Common.{impossible, PrimName}

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TBool
    case TInt
    case TCon(name: GName)

    override def toString: String = this match
      case TBool   => "Bool"
      case TInt    => "Int"
      case TCon(x) => s"$x"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = ps match
      case Nil => rt.toString
      case _   => s"(${ps.mkString(", ")}) -> $rt"
    def head: Ty = ps.head
    def tail: TDef = TDef(ps.tail, rt)
    def ty: Ty =
      if ps.nonEmpty then impossible()
      else rt
    def drop(n: Int): TDef = TDef(ps.drop(n), rt)
  object TDef:
    def apply(rt: Ty): TDef = TDef(Nil, rt)
    def apply(t1: Ty, t2: Ty): TDef = TDef(List(t1), t2)
    def apply(t1: Ty, t2: TDef): TDef = TDef(t1 :: t2.ps, t2.rt)
    def apply(ps: List[Ty], t2: TDef): TDef = TDef(ps ++ t2.ps, t2.rt)

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(
        name: GName,
        gen: Boolean,
        ty: TDef,
        ps: List[(LName, Ty)],
        value: Let
    )
    case DData(name: GName, cons: List[List[Ty]])

    override def toString: String = this match
      case DDef(x, _, t, Nil, v) => s"def $x : $t = $v"
      case DDef(x, _, t, ps, v) =>
        s"def $x ${ps.map((x, t) => s"($x : $t)").mkString(" ")} : ${t.rt} = $v"
      case DData(x, Nil) => s"data $x"
      case DData(x, cs) =>
        s"data $x = ${cs.map(as => s"(${as.mkString(" ")})").mkString(" | ")}"
  export Def.*

  final case class Let(ps: List[(LName, Ty, Comp)], body: Comp):
    override def toString: String =
      if ps.isEmpty then body.toString
      else
        val pss = ps.map((x, t, v) => s"let $x : $t = $v; ").mkString("")
        s"($pss$body)"

  enum Value:
    case Var(name: LName)
    case Global(name: GName, ty: Ty)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case Con(ty: GName, ix: Int, as: List[Value])

    override def toString: String = this match
      case Var(x)       => s"'$x"
      case Global(x, _) => s"$x"

      case IntLit(v)  => s"$v"
      case BoolLit(v) => if v then "True" else "False"

      case Con(t, i, Nil) => s"(con $t #$i)"
      case Con(t, i, as)  => s"(con $t #$i ${as.mkString(" ")})"
  export Value.*

  type CaseEntry = (List[(LName, Ty)], Let)
  enum Comp:
    case Val(value: Value)

    case GlobalApp(name: GName, ty: TDef, tc: Boolean, as: List[Value])
    case PrimApp(name: PrimName, args: List[Value])

    case Case(ty: GName, scrut: Value, cs: List[CaseEntry])

    override def toString: String = this match
      case Val(v) => s"$v"
      case GlobalApp(x, _, tc, as) =>
        s"(${if tc then "[tailcall] " else ""}$x ${as.mkString(" ")})"
      case PrimApp(f, as)   => s"($f ${as.mkString(" ")})"
      case Case(ty, s, Nil) => s"(case $ty $s)"
      case Case(ty, s, cs) =>
        def csStr(c: CaseEntry) = c match
          case (Nil, b) => b.toString
          case (xs, b) =>
            s"(${xs.map((x, t) => s"($x : $t)").mkString(" ")}. $b)"
        s"(case $ty $s ${cs.map(csStr).mkString(" ")})"
  export Comp.*
