package ho

import common.Common.*

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TInt

    override def toString: String = this match
      case TInt => "Int"

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
        module: GName,
        name: GName,
        gen: Boolean,
        ty: TDef,
        value: Tm
    )

    override def toString: String = this match
      case DDef(m, x, _, t, v) => s"def $m:$x : $t = $v"
  export Def.*

  enum Tm:
    case Var(name: LName, ty: TDef)
    case Global(m: GName, name: GName, ty: TDef)

    case IntLit(n: Int)

    case App(fn: Tm, arg: Tm)
    case Lam(name: LName, t1: Ty, t2: TDef, body: Tm)
    case Let(
        name: LName,
        noinline: Boolean,
        ty: TDef,
        bty: TDef,
        value: Tm,
        body: Tm
    )

    case Fix(t1: Ty, t2: TDef, go: LName, x: LName, body: Tm, arg: Tm)

    override def toString: String = this match
      case Var(x, _)       => s"'$x"
      case Global(m, x, _) => s"$m:$x"

      case IntLit(n) => s"$n"

      case App(f, a)             => s"($f $a)"
      case Lam(x, t, _, b)       => s"(\\($x : $t). $b)"
      case Let(x, _, t, _, v, b) => s"(let $x : $t = $v; $b)"

      case Fix(t1, t2, go, x, b, arg) =>
        s"(fix (($go : ${TDef(t1, t2)}) ($x : $t1). $b) $arg)"

    def lams(ps: List[(LName, Ty)], rt: TDef): Tm =
      ps.foldRight[(Tm, TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (Lam(x, t, rt, b), TDef(t, rt))
      }._1

    def flattenLams: (List[(LName, Ty)], Option[Ty], Tm) =
      def go(t: Tm): (List[(LName, Ty)], Option[Ty], Tm) = t match
        case Lam(x, t1, t2, b) =>
          val (xs, rt, b2) = go(b)
          ((x, t1) :: xs, rt.fold(Some(t2.rt))(t => Some(t)), b2)
        case b => (Nil, None, b)
      go(this)

    def apps(args: List[Tm]) = args.foldLeft(this)(App.apply)

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a) =>
        val (hd, as) = f.flattenApps
        (hd, as ++ List(a))
      case t => (t, Nil)

    def fvs: List[(LName, TDef)] = this match
      case Var(x, t)       => List((x, t))
      case Global(_, _, _) => Nil
      case IntLit(_)       => Nil

      case App(f, a)             => f.fvs ++ a.fvs
      case Lam(x, _, _, b)       => b.fvs.filterNot((y, _) => y == x)
      case Let(x, _, _, _, v, b) => v.fvs ++ b.fvs.filterNot((y, _) => x == y)

      case Fix(_, _, go, x, b, arg) =>
        b.fvs.filterNot((y, _) => y == go || y == x) ++ arg.fvs

    def subst(sub: Map[LName, Tm]): Tm =
      subst(
        sub,
        sub.values
          .foldRight(Set.empty[LName])((a, b) => a.fvs.map(_._1).toSet ++ b)
      )
    def subst(sub: Map[LName, Tm], scope: Set[LName]): Tm =
      def underN(
          ps: List[(LName, TDef)],
          b: Tm,
          sub: Map[LName, Tm],
          scope: Set[LName]
      ): (List[(LName, TDef)], Tm) =
        def go(
            ps: List[(LName, TDef)],
            nps: List[(LName, TDef)],
            sub: Map[LName, Tm],
            scope: Set[LName]
        ): (List[(LName, TDef)], Tm) = ps match
          case Nil => (nps, b.subst(sub, scope))
          case (x, t) :: ps =>
            if scope.contains(x) then
              val y = scope.max
              go(
                ps,
                nps ++ List((y, t)),
                sub + (x -> Var(y, t)),
                scope + y
              )
            else go(ps, nps ++ List((x, t)), sub - x, scope + x)
        go(ps, Nil, sub, scope)
      this match
        case Var(x, _)       => sub.get(x).getOrElse(this)
        case Global(_, _, _) => this
        case IntLit(_)       => this

        case App(f, a) => App(f.subst(sub, scope), a.subst(sub, scope))
        case Lam(x0, t1, t2, b0) =>
          val (List((x, _)), b) =
            underN(List((x0, TDef(t1))), b0, sub, scope)
          Lam(x, t1, t2, b)
        case Let(x0, ni, t, bt, v, b0) =>
          val (List((x, _)), b) = underN(List((x0, t)), b0, sub, scope)
          Let(x, ni, t, bt, v.subst(sub, scope), b)

        case Fix(t1, t2, g0, x0, b0, arg) =>
          val (List((g, _), (x, _)), b) = underN(
            List((g0, TDef(t1, t2)), (x0, TDef(t1))),
            b0,
            sub,
            scope
          )
          Fix(t1, t2, g, x, b, arg.subst(sub, scope))
  export Tm.*
