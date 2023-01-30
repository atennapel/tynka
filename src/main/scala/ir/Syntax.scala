package ir

import common.Common.{impossible, PrimName}

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TUnit
    case TBool
    case TInt
    case TPair(fst: Ty, snd: Ty)

    override def toString: String = this match
      case TUnit           => "()"
      case TBool           => "Bool"
      case TInt            => "Int"
      case TPair(fst, snd) => s"($fst, $snd)"
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

    override def toString: String = this match
      case DDef(x, _, t, Nil, v) => s"def $x : $t = $v"
      case DDef(x, _, t, ps, v) =>
        s"def $x ${ps.map((x, t) => s"($x : $t)").mkString(" ")} : $t = $v"
  export Def.*

  final case class Let(ps: List[(LName, Ty, Comp)], ty: Ty, body: Comp):
    override def toString: String =
      if ps.isEmpty then body.toString
      else
        val pss = ps.map((x, t, v) => s"let $x : $t = $v; ").mkString("")
        s"($pss$body)"

  enum Value:
    case Var(name: LName, ty: Ty)
    case Global(name: GName, ty: Ty)

    case Unit
    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case Pair(t1: Ty, t2: Ty, fst: Value, snd: Value)

    override def toString: String = this match
      case Var(x, _)    => s"'$x"
      case Global(x, _) => s"$x"

      case Unit       => "()"
      case IntLit(v)  => s"$v"
      case BoolLit(v) => if v then "True" else "False"

      case Pair(_, _, f, s) => s"($f, $s)"
  export Value.*

  enum Comp:
    case Val(value: Value)

    case GlobalApp(name: GName, ty: TDef, as: List[Value])
    case PrimApp(name: PrimName, args: List[Value])

    case Fst(ty: Ty, tm: Value)
    case Snd(ty: Ty, tm: Value)

    case If(ty: Ty, c: Value, t: Let, f: Let)

    override def toString: String = this match
      case Val(v)              => s"$v"
      case GlobalApp(x, _, as) => s"($x ${as.mkString(" ")})"
      case PrimApp(f, as)      => s"($f ${as.mkString(" ")})"
      case Fst(_, t)           => s"$t.1"
      case Snd(_, t)           => s"$t.2"
      case If(_, c, t, f)      => s"(if $c then $t else $f)"
  export Comp.*
