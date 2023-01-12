package ir

object Syntax:
  type GName = String

  final case class Name(x: Int):
    override def toString: String = s"'$x"

    def fresh(implicit ns: List[Name]): Name = Name.fresh

  object Name:
    def fresh(implicit ns: List[Name]): Name =
      if ns.isEmpty then Name(0) else Name(ns.map(_.x).toSet.max + 1)

  enum Ty:
    case TVoid
    case TUnit
    case TBool
    case TInt
    case TPair(fst: Ty, snd: Ty)
    case TList(ty: Ty)

    override def toString: String = this match
      case TVoid           => "Void"
      case TUnit           => "()"
      case TBool           => "Bool"
      case TInt            => "Int"
      case TPair(fst, snd) => s"($fst, $snd)"
      case TList(t)        => s"List($t)"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = s"(${ps.mkString(", ")}) -> $rt"
  object TDef:
    def apply(rt: Ty): TDef = TDef(Nil, rt)
    def apply(t1: Ty, t2: Ty): TDef = TDef(List(t1), t2)
    def apply(t1: Ty, t2: TDef): TDef = TDef(t1 :: t2.ps, t2.rt)

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

    def returnTy: Ty = this match
      case BEq  => TBool
      case BNeq => TBool
      case BGt  => TBool
      case BLt  => TBool
      case BGeq => TBool
      case BLeq => TBool
      case _    => TInt
  export Op.*

  enum Expr:
    case Var(x: Name)
    case Global(x: GName)
    case App(f: Expr, a: Expr)
    case Lam(x: Name, t1: Ty, t2: TDef, body: Expr)
    case Let(x: Name, ty: TDef, value: Expr, body: Expr)
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

    case LNil
    case LCons(hd: Expr, tl: Expr)
    case CaseList(l: Expr, n: Expr, hd: Name, tl: Name, c: Expr)

    override def toString: String = this match
      case Var(x)             => s"$x"
      case Global(x)          => s"$x"
      case App(f, a)          => s"($f $a)"
      case Lam(x, t, _, b)    => s"(\\($x : $t). $b)"
      case Let(x, t, v, b)    => s"(let $x : $t = $v; $b)"
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

      case LNil                      => "Nil"
      case LCons(hd, tl)             => s"($hd :: $tl)"
      case CaseList(l, n, hd, tl, c) => s"(caseList $l $n ($hd $tl. $c))"

    def flattenLams: (List[(Name, Ty)], Option[Ty], Expr) =
      def go(t: Expr): (List[(Name, Ty)], Option[Ty], Expr) = t match
        case Lam(x, t1, t2, b) =>
          val (xs, rt, b2) = go(b)
          ((x, t1) :: xs, rt.fold(Some(t2.rt))(t => Some(t)), b2)
        case b => (Nil, None, b)
      go(this)

    def flattenApps: (Expr, List[Expr]) = this match
      case App(f, a) =>
        val (hd, as) = f.flattenApps
        (hd, as ++ List(a))
      case t => (t, Nil)

    def lams(ps: List[(Name, Ty)], rt: TDef): Expr =
      ps.foldRight[(Expr, TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (Lam(x, t, rt, b), TDef(t :: rt.ps, rt.rt))
      }._1

    def apps(args: List[Expr]) = args.foldLeft(this)(App.apply)
  export Expr.*
