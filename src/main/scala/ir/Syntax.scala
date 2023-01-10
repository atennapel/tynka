package ir

object Syntax:
  type GName = String

  final case class Name(x: Int):
    override def toString: String = s"'$x"

    def fresh(implicit ns: List[Name]): Name = Name.fresh

  object Name:
    def fresh(implicit ns: List[Name]): Name =
      if ns.isEmpty then Name(0) else Name(ns.map(_.x).toSet.max + 1)

  enum Type:
    case TVoid
    case TUnit
    case TBool
    case TPair(fst: Type, snd: Type)

    override def toString: String = this match
      case TVoid           => "Void"
      case TUnit           => "()"
      case TBool           => "Bool"
      case TPair(fst, snd) => s"($fst, $snd)"
  export Type.*

  final case class TDef(ps: List[Type], rt: Type):
    override def toString: String = s"(${ps.mkString(", ")}) -> $rt"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: GName, ty: TDef, value: Expr)

    override def toString: String = this match
      case DDef(x, t, v) => s"def $x : $t = $v"
  export Def.*

  enum Expr:
    case Var(x: Name)
    case Global(x: GName)
    case App(f: Expr, as: List[Expr])
    case Lam(ps: List[Name], body: Expr)
    case Let(x: Name, value: Expr, body: Expr)

    case Pair(fst: Expr, snd: Expr)
    case Fst(tm: Expr)
    case Snd(tm: Expr)

    case Absurd

    case Unit

    case BoolLit(bool: Boolean)
    case If(cond: Expr, ifTrue: Expr, ifFalse: Expr)

    override def toString: String = this match
      case Var(x)       => s"$x"
      case Global(x)    => s"$x"
      case App(f, as)   => s"$f(${as.mkString(", ")})"
      case Lam(ps, b)   => s"(\\${ps.mkString(" ")}. $b)"
      case Let(x, v, b) => s"(let $x = $v; $b)"

      case Pair(fst, snd) => s"($fst, $snd)"
      case Fst(t)         => s"$t.1"
      case Snd(t)         => s"$t.2"

      case Absurd => s"absurd"

      case Unit => "()"

      case BoolLit(true)  => "True"
      case BoolLit(false) => "False"
      case If(c, a, b)    => s"(if $c then $a else $b)"
  export Expr.*
