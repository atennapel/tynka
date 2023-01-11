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
    case TInt
    case TPair(fst: Type, snd: Type)
    case TList(ty: Type)

    override def toString: String = this match
      case TVoid           => "Void"
      case TUnit           => "()"
      case TBool           => "Bool"
      case TInt            => "Int"
      case TPair(fst, snd) => s"($fst, $snd)"
      case TList(t)        => s"List($t)"
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

  enum Op:
    case BAdd
    case BMul
    case BSub
    case BDiv
    case BMod
    case BEq
    case BNeq
    case BGt
    case BLt
    case BGeq
    case BLeq

    override def toString: String = this match
      case BAdd => "+"
      case BMul => "*"
      case BSub => "-"
      case BDiv => "/"
      case BMod => "%"
      case BEq  => "=="
      case BNeq => "!="
      case BGt  => ">"
      case BLt  => "<"
      case BGeq => ">="
      case BLeq => "<="
  export Op.*

  enum Expr:
    case Var(x: Name)
    case Global(x: GName)
    case App(f: Expr, as: List[Expr])
    case Lam(ps: List[Name], body: Expr)
    case Let(x: Name, value: Expr, body: Expr)
    case Fix(go: Name, x: Name, body: Expr, arg: Expr)

    case Pair(fst: Expr, snd: Expr)
    case Fst(tm: Expr)
    case Snd(tm: Expr)

    case IntLit(value: Int)
    case BinOp(op: Op, a: Expr, b: Expr)

    case Absurd

    case Unit

    case BoolLit(bool: Boolean)
    case If(cond: Expr, ifTrue: Expr, ifFalse: Expr)

    case Nil
    case Cons(hd: Expr, tl: Expr)
    case CaseList(l: Expr, n: Expr, hd: Name, tl: Name, c: Expr)

    override def toString: String = this match
      case Var(x)             => s"$x"
      case Global(x)          => s"$x"
      case App(f, as)         => s"($f ${as.mkString(" ")})"
      case Lam(ps, b)         => s"(\\${ps.mkString(" ")}. $b)"
      case Let(x, v, b)       => s"(let $x = $v; $b)"
      case Fix(go, x, b, arg) => s"(fix ($go $x. $b) $arg)"

      case Pair(fst, snd) => s"($fst, $snd)"
      case Fst(t)         => s"$t.1"
      case Snd(t)         => s"$t.2"

      case IntLit(n)       => s"$n"
      case BinOp(op, a, b) => s"($a $op $b)"

      case Absurd => s"absurd"

      case Unit => "()"

      case BoolLit(true)  => "True"
      case BoolLit(false) => "False"
      case If(c, a, b)    => s"(if $c then $a else $b)"

      case Nil                       => "Nil"
      case Cons(hd, tl)              => s"($hd :: $tl)"
      case CaseList(l, n, hd, tl, c) => s"(caseList $l $n ($hd $tl. $c))"
  export Expr.*
