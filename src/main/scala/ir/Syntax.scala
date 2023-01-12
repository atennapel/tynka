package ir

object Syntax:
  type GName = String

  final case class Name(expose: Int):
    override def toString: String = s"'$expose"

    def fresh(implicit ns: List[Name]): Name = Name.fresh

  object Name:
    def fresh(implicit ns: List[Name]): Name =
      if ns.isEmpty then Name(0) else Name(ns.map(_.expose).toSet.max + 1)

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
    def tail: TDef = TDef(ps.tail, rt)
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
    case Var(x: Name, ty: TDef)
    case Global(x: GName, ty: TDef)
    case App(f: Expr, a: Expr)
    case Lam(x: Name, t1: Ty, t2: TDef, body: Expr)
    case Let(x: Name, ty: TDef, bt: TDef, value: Expr, body: Expr)
    case Fix(go: Name, x: Name, t1: Ty, t2: TDef, body: Expr, arg: Expr)

    case Pair(fst: Expr, snd: Expr)
    case Fst(tm: Expr)
    case Snd(tm: Expr)

    case IntLit(value: Int)
    case BinOp(op: Op, a: Expr, b: Expr)

    case Absurd

    case Unit

    case BoolLit(bool: Boolean)
    case If(ty: TDef, cond: Expr, ifTrue: Expr, ifFalse: Expr)

    case LNil(ty: Ty)
    case LCons(ty: Ty, hd: Expr, tl: Expr)
    case CaseList(
        t1: Ty,
        t2: TDef,
        l: Expr,
        n: Expr,
        hd: Name,
        tl: Name,
        c: Expr
    )

    override def toString: String = this match
      case Var(x, _)                => s"$x"
      case Global(x, _)             => s"$x"
      case App(f, a)                => s"($f $a)"
      case Lam(x, t, _, b)          => s"(\\($x : $t). $b)"
      case Let(x, t, _, v, b)       => s"(let $x : $t = $v; $b)"
      case Fix(go, x, _, _, b, arg) => s"(fix ($go $x. $b) $arg)"

      case Pair(fst, snd) => s"($fst, $snd)"
      case Fst(t)         => s"$t.1"
      case Snd(t)         => s"$t.2"

      case IntLit(n)       => s"$n"
      case BinOp(op, a, b) => s"($a $op $b)"

      case Absurd => s"absurd"

      case Unit => "()"

      case BoolLit(true)  => "True"
      case BoolLit(false) => "False"
      case If(_, c, a, b) => s"(if $c then $a else $b)"

      case LNil(_)                         => "Nil"
      case LCons(_, hd, tl)                => s"($hd :: $tl)"
      case CaseList(_, _, l, n, hd, tl, c) => s"(caseList $l $n ($hd $tl. $c))"

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

    def size: Int = this match
      case Var(x, t)                => 1
      case Global(x, _)             => 1
      case App(f, a)                => 1 + f.size + a.size
      case Lam(x, _, _, b)          => 1 + b.size
      case Let(x, _, _, v, b)       => 1 + v.size + b.size
      case Fix(go, x, _, _, b, arg) => 1 + b.size + arg.size

      case Pair(fst, snd) => 1 + fst.size + snd.size
      case Fst(t)         => 1 + t.size
      case Snd(t)         => 1 + t.size

      case IntLit(n)       => 1
      case BinOp(op, a, b) => 1 + a.size + b.size

      case Absurd => 1

      case Unit => 1

      case BoolLit(_)     => 1
      case If(_, c, a, b) => 1 + c.size + a.size + b.size

      case LNil(_)                         => 1
      case LCons(_, hd, tl)                => 1 + hd.size + tl.size
      case CaseList(_, _, l, n, hd, tl, c) => 1 + l.size + n.size + c.size

    def fvs: List[(Name, TDef)] = this match
      case Var(x, t)          => List((x, t))
      case Global(x, _)       => Nil
      case App(f, a)          => f.fvs ++ a.fvs
      case Lam(x, _, _, b)    => b.fvs.filterNot((y, _) => x == y)
      case Let(x, _, _, v, b) => v.fvs ++ b.fvs.filterNot((y, _) => x == y)
      case Fix(go, x, _, _, b, arg) =>
        b.fvs.filterNot((y, _) => x == y || go == y) ++ arg.fvs

      case Pair(fst, snd) => fst.fvs ++ snd.fvs
      case Fst(t)         => t.fvs
      case Snd(t)         => t.fvs

      case IntLit(n)       => Nil
      case BinOp(op, a, b) => a.fvs ++ b.fvs

      case Absurd => Nil

      case Unit => Nil

      case BoolLit(_)     => Nil
      case If(_, c, a, b) => c.fvs ++ a.fvs ++ b.fvs

      case LNil(_)          => Nil
      case LCons(_, hd, tl) => hd.fvs ++ tl.fvs
      case CaseList(_, _, l, n, hd, tl, c) =>
        l.fvs ++ n.fvs ++ c.fvs.filterNot((y, _) => y == hd || y == tl)

    def subst(sub: Map[Name, Expr]): Expr =
      subst(
        sub,
        sub.values
          .foldRight(Set.empty[Int])((a, b) =>
            a.fvs.map(_._1.expose).toSet ++ b
          )
      )
    def subst(sub: Map[Name, Expr], scope: Set[Int]): Expr =
      def under(
          x: Name,
          t: TDef,
          b: Expr,
          sub: Map[Name, Expr],
          scope: Set[Int]
      ): (Name, Expr) =
        if scope.contains(x.expose) then
          val y = scope.max + 1
          val ny = Name(y)
          (ny, b.subst(sub + (x -> Var(ny, t)), scope + y))
        else (x, b.subst(sub - x, scope + x.expose))
      def under2(
          x0: Name,
          t1: TDef,
          y0: Name,
          t2: TDef,
          b: Expr,
          sub: Map[Name, Expr],
          scope: Set[Int]
      ): (Name, Name, Expr) =
        if !scope.contains(x0.expose) && !scope.contains(y0.expose) then
          (x0, y0, b.subst(sub - x0 - y0, scope + x0.expose + y0.expose))
        else if scope.contains(x0.expose) && !scope.contains(y0.expose) then
          val x = scope.max + 1
          val nx = Name(x)
          (nx, y0, b.subst(sub + (x0 -> Var(nx, t1)), scope + x + y0.expose))
        else if !scope.contains(x0.expose) && scope.contains(y0.expose) then
          val y = scope.max + 1
          val ny = Name(y)
          (x0, ny, b.subst(sub + (y0 -> Var(ny, t2)), scope + x0.expose + y))
        else
          val m = scope.max
          val x = m + 1
          val y = m + 2
          val nx = Name(x)
          val ny = Name(y)
          (
            nx,
            ny,
            b.subst(
              sub + (x0 -> Var(nx, t1)) + (y0 -> Var(ny, t2)),
              scope + x + y
            )
          )
      this match
        case Var(x, _)    => sub.get(x).getOrElse(this)
        case Global(_, _) => this
        case App(f, a)    => App(f.subst(sub, scope), a.subst(sub, scope))
        case Lam(x0, t1, t2, b0) =>
          val (x, b) = under(x0, TDef(t1), b0, sub, scope)
          Lam(x, t1, t2, b)
        case Let(x0, t, bt, v, b0) =>
          val (x, b) = under(x0, t, b0, sub, scope)
          Let(x, t, bt, v.subst(sub, scope), b)
        case Fix(go0, x0, t1, t2, b0, arg) =>
          val (go, x, b) =
            under2(go0, TDef(t1, t2), x0, TDef(t1), b0, sub, scope)
          Fix(go, x, t1, t2, b, arg.subst(sub, scope))

        case Pair(fst, snd) =>
          Pair(fst.subst(sub, scope), snd.subst(sub, scope))
        case Fst(t) => Fst(t.subst(sub, scope))
        case Snd(t) => Snd(t.subst(sub, scope))

        case IntLit(n) => this
        case BinOp(op, a, b) =>
          BinOp(op, a.subst(sub, scope), b.subst(sub, scope))

        case Absurd => this

        case Unit => this

        case BoolLit(_) => this
        case If(t, c, a, b) =>
          If(t, c.subst(sub, scope), a.subst(sub, scope), b.subst(sub, scope))

        case LNil(_) => this
        case LCons(t, hd, tl) =>
          LCons(t, hd.subst(sub, scope), tl.subst(sub, scope))
        case CaseList(t1, t2, l, n, hd0, tl0, c0) =>
          val (hd, tl, c) = under2(hd0, TDef(t1), tl0, t2, c0, sub, scope)
          CaseList(t1, t2, l.subst(sub, scope), n.subst(sub, scope), hd, tl, c)
  export Expr.*
  object Expr:
    def fromBool(b: Boolean): Expr = BoolLit(b)
