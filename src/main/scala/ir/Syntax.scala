package ir

import common.Common.{impossible, PrimName}

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TUnit
    case TBool
    case TInt
    case TBox
    case TCon(name: GName)
    case TForeign(cls: String)

    override def toString: String = this match
      case TUnit         => "Unit"
      case TBool         => "Bool"
      case TInt          => "Int"
      case TBox          => s"Box"
      case TCon(x)       => s"$x"
      case TForeign(cls) => s"Foreign($cls)"

    def tdef: TDef = TDef(this)
  export Ty.*

  final case class TDef(ps: Option[List[Ty]], rt: Ty):
    override def toString: String = ps match
      case None => rt.toString
      case _    => s"(${ps.mkString(", ")}) -> $rt"
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
        module: GName,
        name: GName,
        gen: Boolean,
        ty: TDef,
        ps: List[(LName, Ty)],
        value: Expr
    )
    case DData(name: GName, cons: List[List[Ty]])

    override def toString: String = this match
      case DDef(m, x, _, TDef(None, t), _, v) => s"def $m:$x : $t = $v"
      case DDef(m, x, _, t, Nil, v)           => s"def $m:$x () : $t = $v"
      case DDef(m, x, _, t, ps, v) =>
        s"def $m:$x ${ps.map((x, t) => s"($x : $t)").mkString(" ")} : ${t.rt} = $v"
      case DData(x, Nil) => s"data $x"
      case DData(x, cs) =>
        s"data $x = ${cs.map(as => s"(${as.mkString(" ")})").mkString(" | ")}"
  export Def.*

  enum Expr:
    case Var(name: LName)
    case Global(module: GName, name: GName, ty: Ty)

    case Let(name: LName, isUsed: Boolean, ty: Ty, value: Expr, body: Expr)

    case GlobalApp(
        module: GName,
        name: GName,
        ty: TDef,
        tc: Boolean,
        as: List[Expr]
    )
    case PrimApp(name: PrimName, args: List[Expr])
    case Foreign(rt: Ty, cmd: String, args: List[(Expr, Ty)])

    case UnitLit
    case IntLit(value: Int)
    case BoolLit(value: Boolean)
    case StringLit(value: String)

    case Con(ty: GName, ix: Int, as: List[Expr])
    case Case(ty: GName, scrut: Expr, x: LName, cs: List[Expr])
    case Field(ty: GName, rty: Ty, conix: Int, ix: Int, tm: Expr)

    case Box(ty: Ty, value: Expr)
    case Unbox(ty: Ty, v: Expr)

    override def toString: String = this match
      case Var(x)                 => s"'$x"
      case Global(m, x, _)        => s"$m:$x"
      case Let(x, false, t, v, b) => s"(let _ : $t = $v; $b)"
      case Let(x, _, t, v, b)     => s"(let $x : $t = $v; $b)"

      case UnitLit      => "()"
      case IntLit(v)    => s"$v"
      case BoolLit(v)   => if v then "True" else "False"
      case StringLit(v) => s"\"$v\""

      case Con(t, i, Nil) => s"(con $t #$i)"
      case Con(t, i, as)  => s"(con $t #$i ${as.mkString(" ")})"

      case Box(_, v) => s"(box $v)"

      case GlobalApp(m, x, _, tc, as) =>
        s"(${if tc then "[tailcall] " else ""}$m:$x ${as.mkString(" ")})"
      case PrimApp(f, as)        => s"($f ${as.mkString(" ")})"
      case Case(ty, s, x, Nil)   => s"(case $x : $ty = $s)"
      case Case(ty, s, x, cs)    => s"(case $x : $ty = $s; ${cs.mkString(" ")})"
      case Field(_, _, ci, i, v) => s"(field $ci#$i $v)"
      case Unbox(_, v)           => s"(unbox $v)"
      case Foreign(rt, cmd, Nil) => s"(foreign $rt $cmd)"
      case Foreign(rt, cmd, as) =>
        s"(foreign $rt $cmd ${as.map((v, t) => s"$v").mkString(" ")})"
  export Expr.*
