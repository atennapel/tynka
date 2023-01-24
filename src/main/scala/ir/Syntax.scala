package ir

import common.Common.impossible

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
    case TEither(a: Ty, b: Ty)
    case TList(ty: Ty)

    override def toString: String = this match
      case TVoid           => "Void"
      case TUnit           => "()"
      case TBool           => "Bool"
      case TInt            => "Int"
      case TPair(fst, snd) => s"($fst, $snd)"
      case TEither(a, b)   => s"Either $a $b"
      case TList(t)        => s"List $t"
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
    case DDef(name: GName, ty: TDef, ps: List[(Name, Ty)], value: Let)

    override def toString: String = this match
      case DDef(x, t, Nil, v) => s"def $x : ${t.rt} = $v"
      case DDef(x, t, ps, v) =>
        s"def $x ${ps.map((x, t) => s"($x : $t)").mkString(" ")} : ${t.rt} = $v"
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

  enum Value:
    case Var(x: Name, ty: TDef)
    case Global(x: GName, ty: TDef)

    case Unit
    case BoolLit(bool: Boolean)
    case IntLit(value: Int)

    case Pair(t1: Ty, t2: Ty, fst: Value, snd: Value)

    case LNil(ty: Ty)
    case LCons(ty: Ty, hd: Value, tl: Value)

    case ELeft(t1: Ty, t2: Ty, v: Value)
    case ERight(t1: Ty, t2: Ty, v: Value)

    override def toString: String = this match
      case Var(x, _)    => s"$x"
      case Global(x, _) => s"$x"

      case Pair(_, _, fst, snd) => s"($fst, $snd)"

      case IntLit(n)      => s"$n"
      case Unit           => "()"
      case BoolLit(true)  => "True"
      case BoolLit(false) => "False"

      case LNil(_)          => "Nil"
      case LCons(_, hd, tl) => s"($hd :: $tl)"

      case ELeft(_, _, v)  => s"(Left $v)"
      case ERight(_, _, v) => s"(Right $v)"

    def fvs: List[(Name, TDef)] = this match
      case Var(x, t)    => List((x, t))
      case Global(x, _) => Nil

      case Pair(_, _, fst, snd) => fst.fvs ++ snd.fvs

      case IntLit(n)  => Nil
      case Unit       => Nil
      case BoolLit(_) => Nil

      case LNil(_)          => Nil
      case LCons(_, hd, tl) => hd.fvs ++ tl.fvs

      case ELeft(_, _, v)  => v.fvs
      case ERight(_, _, v) => v.fvs

    def subst(sub: Map[Name, Value]): Value =
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
      def underN(
          ps: List[(Name, TDef)],
          b: Expr,
          sub: Map[Name, Expr],
          scope: Set[Int]
      ): (List[(Name, TDef)], Expr) =
        def go(
            ps: List[(Name, TDef)],
            nps: List[(Name, TDef)],
            sub: Map[Name, Expr],
            scope: Set[Int]
        ): (List[(Name, TDef)], Expr) = ps match
          case Nil => (nps, b.subst(sub, scope))
          case (x, t) :: ps =>
            if scope.contains(x.expose) then
              val y = scope.max
              val ny = Name(y)
              go(
                ps,
                nps ++ List((ny, t)),
                sub + (x -> Var(ny, t)),
                scope + y
              )
            else go(ps, nps ++ List((x, t)), sub - x, scope + x.expose)
        go(ps, Nil, sub, scope)
      this match
        case Var(x, _)    => sub.get(x).getOrElse(this)
        case Global(_, _) => this
        case App(f, a)    => App(f.subst(sub, scope), a.subst(sub, scope))
        case Let(x0, t, bt, v, b0) =>
          val (x, b) = under(x0, TDef(t), b0, sub, scope)
          Let(x, t, bt, v.subst(sub, scope), b)

        case LetLift(x, t, ps0, bt, v, b0) =>
          val (ps, b) = underN(ps0.map((x, t) => (x, TDef(t))), b0, sub, scope)
          LetLift(x, t, ps.map((x, t) => (x, t.rt)), bt, v.subst(sub, scope), b)

        case Fix(go0, x0, t1, t2, ps0, b0, arg) =>
          val (ps, b) =
            underN(
              List((go0, TDef(t1, t2)), (x0, TDef(t1))) ++ ps0.map((x, t) =>
                (x, TDef(t))
              ),
              b0,
              sub,
              scope
            )
          Fix(
            ps(0)._1,
            ps(1)._1,
            t1,
            t2,
            ps.drop(2).map((x, t) => (x, t.rt)),
            b,
            arg.subst(sub, scope)
          )

        case Pair(t1, t2, fst, snd) =>
          Pair(t1, t2, fst.subst(sub, scope), snd.subst(sub, scope))
        case Fst(ty, t) => Fst(ty, t.subst(sub, scope))
        case Snd(ty, t) => Snd(ty, t.subst(sub, scope))

        case IntLit(n) => this
        case BinOp(op, a, b) =>
          BinOp(op, a.subst(sub, scope), b.subst(sub, scope))

        case Absurd(_) => this

        case Unit => this

        case BoolLit(_) => this
        case If(t, c, a, b) =>
          If(t, c.subst(sub, scope), a.subst(sub, scope), b.subst(sub, scope))

        case LNil(_) => this
        case LCons(t, hd, tl) =>
          LCons(t, hd.subst(sub, scope), tl.subst(sub, scope))
        case CaseList(t1, t2, l, n, hd0, tl0, c0) =>
          val (hd, tl, c) = under2(hd0, TDef(t1), tl0, TDef(t2), c0, sub, scope)
          CaseList(t1, t2, l.subst(sub, scope), n.subst(sub, scope), hd, tl, c)

        case ELeft(t1, t2, v)  => ELeft(t1, t2, v.subst(sub, scope))
        case ERight(t1, t2, v) => ERight(t1, t2, v.subst(sub, scope))
        case CaseEither(t1, t2, rt, v, x0, l0, y0, r0) =>
          val (x, l) = under(x0, TDef(t1), l0, sub, scope)
          val (y, r) = under(y0, TDef(t2), r0, sub, scope)
          CaseEither(t1, t2, rt, v.subst(sub, scope), x, l, y, r)
  export Value.*

  enum Comp:
    case Val(value: Value)

    case App(f: Value, as: List[Value])

    case Lam(ps: List[(Name, Ty)], t2: TDef, body: Let)

    case Fix(
        t1: Ty,
        t2: TDef,
        go: Name,
        x: Name,
        ps: List[(Name, Ty)],
        body: Let,
        arg: Value
    )

    case Fst(ty: Ty, tm: Value)
    case Snd(ty: Ty, tm: Value)

    case BinOp(op: Op, a: Value, b: Value)

    case Absurd(ty: TDef)
    case If(ty: Ty, cond: Value, ifTrue: Let, ifFalse: Let)
    case CaseList(
        t1: Ty,
        t2: Ty,
        l: Value,
        n: Let,
        hd: Name,
        tl: Name,
        c: Let
    )
    case CaseEither(
        t1: Ty,
        t2: Ty,
        rt: Ty,
        v: Value,
        x: Name,
        l: Let,
        y: Name,
        r: Let
    )

    override def toString: String = this match
      case Val(v)     => s"$v"
      case App(f, as) => s"($f ${as.mkString(" ")})"
      case Fix(t1, t2, go, x, Nil, b, arg) =>
        s"(fix (($go : ${TDef(t1, t2)}) ($x : $t1). $b) $arg)"
      case Fix(t1, t2, go, x, ps, b, arg) =>
        s"(fix (($go : ${TDef(t1, t2)}) ($x : $t1) ${ps
            .map((x, t) => s"($x : $t)")
            .mkString(" ")}. $b) $arg)"
      case Lam(ps, _, b) =>
        s"(\\${ps.map((x, t) => s"($x : $t)").mkString(" ")}. $b)"

      case Fst(_, t) => s"$t.1"
      case Snd(_, t) => s"$t.2"

      case BinOp(op, a, b) => s"($a $op $b)"

      case Absurd(_)                       => s"absurd"
      case If(_, c, a, b)                  => s"(if $c then $a else $b)"
      case CaseList(_, _, l, n, hd, tl, c) => s"(caseList $l $n ($hd $tl. $c))"
      case CaseEither(_, _, _, v, x, l, y, r) =>
        s"(caseEither $v ($x. $l) ($y. $r))"

    def fvs: List[(Name, TDef)] = this match
      case Val(v)     => v.fvs
      case App(f, as) => f.fvs ++ as.map(_.fvs).flatten
      case Lam(ps, _, b) =>
        b.fvs.filterNot((y, _) => ps.exists((x, _) => x == y))
      case Fix(_, _, go, x, ps, b, arg) =>
        b.fvs.filterNot((y, _) =>
          x == y || go == y || ps.exists((z, _) => z == y)
        ) ++ arg.fvs

      case Fst(_, t) => t.fvs
      case Snd(_, t) => t.fvs

      case BinOp(op, a, b) => a.fvs ++ b.fvs

      case Absurd(_)      => Nil
      case If(_, c, a, b) => c.fvs ++ a.fvs ++ b.fvs
      case CaseList(_, _, l, n, hd, tl, c) =>
        l.fvs ++ n.fvs ++ c.fvs.filterNot((y, _) => y == hd || y == tl)
      case CaseEither(_, _, _, v, x, l, y, r) =>
        v.fvs ++ l.fvs.filterNot((z, _) => z == x) ++ r.fvs
          .filterNot((z, _) => z == y)
  export Comp.*

  type Lets = List[(Name, Ty, Comp)]
  final case class Let(ds: Lets, ty: TDef, body: Comp):
    override def toString: String =
      val lets: String = ds
        .map { case (x, t, v) => s"let $x : $t = $v; " }
        .mkString("")
      s"($lets$body)"

    def fvs: List[(Name, TDef)] =
      body.fvs.filterNot((y, _) => ds.exists((x, _, _) => x == y))
