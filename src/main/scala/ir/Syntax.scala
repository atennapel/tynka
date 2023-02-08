package ir

import common.Common.{impossible, PrimName}

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TBool
    case TInt
    case TCon(name: GName)
    case TBox
    case TForeign(cls: String)

    override def toString: String = this match
      case TBool         => "Bool"
      case TInt          => "Int"
      case TCon(x)       => s"$x"
      case TBox          => s"Box"
      case TForeign(cls) => s"Foreign($cls)"
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

    def fv: Set[LName] =
      ps.foldRight(body.fv) { case ((x, _, v), fv) => (fv - x) ++ v.fv }

  enum Value:
    case Var(name: LName)
    case Global(module: GName, name: GName, ty: Ty)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)
    case StringLit(value: String)

    case Con(ty: GName, ix: Int, as: List[Value])

    case Box(ty: Ty, value: Value)

    override def toString: String = this match
      case Var(x)          => s"'$x"
      case Global(m, x, _) => s"$m:$x"

      case IntLit(v)    => s"$v"
      case BoolLit(v)   => if v then "True" else "False"
      case StringLit(v) => s"\"$v\""

      case Con(t, i, Nil) => s"(con $t #$i)"
      case Con(t, i, as)  => s"(con $t #$i ${as.mkString(" ")})"

      case Box(_, v) => s"(box $v)"

    def fv: Set[LName] = this match
      case Var(x)        => Set(x)
      case Con(_, _, as) => as.flatMap(_.fv).toSet
      case Box(_, v)     => v.fv
      case _             => Set.empty
  export Value.*

  type CaseEntry = (List[(LName, Ty)], Let)
  enum Comp:
    case Val(value: Value)

    case GlobalApp(
        module: GName,
        name: GName,
        ty: TDef,
        tc: Boolean,
        as: List[Value]
    )
    case PrimApp(name: PrimName, args: List[Value])

    case Case(ty: GName, scrut: Value, cs: List[CaseEntry])

    case Unbox(ty: Ty, v: Value)

    case Foreign(rt: Ty, cmd: String, args: List[(Value, Ty)])

    override def toString: String = this match
      case Val(v) => s"$v"
      case GlobalApp(m, x, _, tc, as) =>
        s"(${if tc then "[tailcall] " else ""}$m:$x ${as.mkString(" ")})"
      case PrimApp(f, as)   => s"($f ${as.mkString(" ")})"
      case Case(ty, s, Nil) => s"(case $ty $s)"
      case Case(ty, s, cs) =>
        def csStr(c: CaseEntry) = c match
          case (Nil, b) => b.toString
          case (xs, b) =>
            s"(${xs.map((x, t) => s"($x : $t)").mkString(" ")}. $b)"
        s"(case $ty $s ${cs.map(csStr).mkString(" ")})"
      case Unbox(_, v)           => s"(unbox $v)"
      case Foreign(rt, cmd, Nil) => s"(foreign $rt $cmd)"
      case Foreign(rt, cmd, as) =>
        s"(foreign $rt $cmd ${as.map((v, t) => s"$v").mkString(" ")})"

    def fv: Set[LName] = this match
      case Val(v)                    => v.fv
      case GlobalApp(_, _, _, _, as) => as.flatMap(_.fv).toSet
      case PrimApp(_, as)            => as.flatMap(_.fv).toSet
      case Case(_, s, cs) => s.fv ++ cs.flatMap((xs, b) => b.fv -- xs.map(_._1))
      case Unbox(_, v)    => v.fv
      case Foreign(_, _, as) => as.flatMap(_._1.fv).toSet
  export Comp.*
