package ir

import common.Common.impossible

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TCon(x: GName)
    case TForeign(x: String)

    override def toString: String = this match
      case TCon(x)     => s"$x"
      case TForeign(x) => s"Foreign($x)"

    def tdef: TDef = TDef(this)
  export Ty.*

  final case class TDef(ps: List[Ty], io: Boolean, rt: Ty):
    override def toString: String = ps match
      case Nil if !io => rt.toString
      case _ => s"(${ps.mkString(", ")}) ->${if io then " IO" else ""} $rt"
    def head: Ty = ps.head
    def tail: TDef = TDef(ps.tail, io, rt)
    def ty: Ty =
      if ps.nonEmpty || io then impossible()
      else rt
    def drop(n: Int): TDef = TDef(ps.drop(n), io, rt)
    def params: List[Ty] = ps
  object TDef:
    def apply(rt: Ty): TDef = TDef(Nil, false, rt)
    def apply(io: Boolean, rt: Ty): TDef = TDef(Nil, io, rt)
    def apply(t1: Ty, t2: Ty): TDef = TDef(List(t1), false, t2)
    def apply(t1: Ty, t2: TDef): TDef = TDef(t1 :: t2.ps, t2.io, t2.rt)
    def apply(ps: List[Ty], t2: TDef): TDef = TDef(ps ++ t2.ps, t2.io, t2.rt)

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case DDef(name: GName, gen: Boolean, ty: TDef, value: Tm)
    case DData(
        name: GName,
        cs: List[(GName, List[Ty])]
    )

    override def toString: String = this match
      case DDef(x, _, t, v) => s"def $x : $t = $v"
      case DData(x, Nil)    => s"data $x"
      case DData(x, cs) =>
        s"data $x = ${cs
            .map((x, ts) => s"$x${if ts.isEmpty then "" else " "}${ts.mkString(" ")}")
            .mkString(" | ")}"
  export Def.*

  enum Tm:
    case Var(name: LName, ty: TDef)
    case Global(name: GName, ty: TDef)

    case IntLit(n: Int)
    case BoolLit(b: Boolean)
    case StringLit(s: String)

    case App(fn: Tm, arg: Tm)
    case Lam(name: LName, t1: Ty, t2: TDef, body: Tm)
    case Fix(ty: Ty, rty: TDef, g: LName, x: LName, b: Tm, arg: Tm)
    case Let(
        name: LName,
        ty: TDef,
        bty: TDef,
        value: Tm,
        body: Tm
    )

    case Con(name: GName, con: GName, args: List[Tm])
    case Field(dty: GName, con: GName, scrut: Tm, ix: Int)
    case Match(
        dty: GName,
        rty: TDef,
        x: LName,
        scrut: Tm,
        cs: List[(GName, Tm)],
        other: Option[Tm]
    )

    case ReturnIO(value: Tm)
    case BindIO(t1: Ty, t2: Ty, x: LName, value: Tm, body: Tm)

    case Foreign(rt: Ty, cmd: String, args: List[(Tm, Ty)])

    override def toString: String = this match
      case Var(x, _)    => s"'$x"
      case Global(x, _) => s"$x"

      case IntLit(n)    => s"$n"
      case BoolLit(n)   => s"$n"
      case StringLit(s) => s"\"$s\""

      case App(f, a)               => s"($f $a)"
      case Lam(x, t, _, b)         => s"(\\($x : $t). $b)"
      case Fix(_, _, g, x, b, arg) => s"(fix ($g $x. $b) $arg)"
      case Let(x, t, _, v, b)      => s"(let $x : $t = $v; $b)"

      case Con(_, "Z", Nil) => "0"
      case full @ Con(_, "S", as @ List(n)) =>
        def tryNat(n: Tm): Option[Int] = n match
          case Con(_, "Z", Nil)     => Some(0)
          case Con(_, "S", List(n)) => tryNat(n).map(_ + 1)
          case _                    => None
        tryNat(full).map(_.toString).getOrElse(s"(con S ${as.mkString(" ")})")
      case Con(x, cx, Nil)   => s"(con $cx)"
      case Con(x, cx, as)    => s"(con $cx ${as.mkString(" ")})"
      case Field(_, _, s, i) => s"(field #$i $s)"

      case Match(_, _, x, scrut, cs, other) =>
        s"(match $x = $scrut; ${cs
            .map((c, b) => s"| $c $b")
            .mkString(" ")} ${other.map(t => s"| $t").getOrElse("")})"

      case ReturnIO(v)           => s"(returnIO $v)"
      case BindIO(_, _, x, v, b) => s"($x <- $v; $b)"

      case Foreign(rt, l, Nil) => s"(foreign $rt $l)"
      case Foreign(rt, l, as) =>
        s"(foreign $rt $l ${as.map(_._1).mkString(" ")})"

    def lams(ps: List[(LName, Ty)], rt: TDef): Tm =
      ps.foldRight[(Tm, TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (Lam(x, t, rt, b), TDef(t, rt))
      }._1

    def flattenLams: (Option[(List[(LName, Ty)], TDef)], Tm) =
      def go(t: Tm): (Option[(List[(LName, Ty)], TDef)], Tm) = t match
        case Lam(x, t1, t2, b) =>
          val (opt, b2) = go(b)
          opt match
            case None => (Some((List((x, t1)), t2)), b2)
            case Some((xs, rt)) =>
              (Some(((x, t1) :: xs, rt)), b2)
        case b => (None, b)
      go(this)

    def apps(args: List[Tm]) = args.foldLeft(this)(App.apply)

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a) =>
        val (hd, as) = f.flattenApps
        (hd, as ++ List(a))
      case t => (t, Nil)

    // may contain duplicates, to be used for usage counts
    def fvs: List[(LName, TDef)] = this match
      case Var(x, t)    => List((x, t))
      case Global(_, _) => Nil
      case IntLit(_)    => Nil
      case BoolLit(_)   => Nil
      case StringLit(_) => Nil

      case App(f, a)       => f.fvs ++ a.fvs
      case Lam(x, _, _, b) => b.fvs.filterNot((y, _) => y == x)
      case Fix(_, _, go, x, b, arg) =>
        b.fvs.filterNot((y, _) => y == go || y == x) ++ arg.fvs
      case Let(x, _, _, v, b) => v.fvs ++ b.fvs.filterNot((y, _) => x == y)

      case Con(x, cx, as)    => as.flatMap(_.fvs)
      case Field(_, _, s, i) => s.fvs
      case Match(_, _, x, s, cs, o) =>
        s.fvs ++ cs.flatMap(_._2.fvs.filterNot((y, _) => x == y)) ++ o
          .map(_.fvs)
          .getOrElse(Nil)

      case ReturnIO(v)           => v.fvs
      case BindIO(_, _, x, v, b) => v.fvs ++ b.fvs.filterNot((y, _) => x == y)

      case Foreign(_, _, as) => as.flatMap(_._1.fvs)

    def usedNames: Set[LName] = this match
      case Var(x, _)    => Set(x)
      case Global(_, _) => Set.empty
      case IntLit(_)    => Set.empty
      case BoolLit(_)   => Set.empty
      case StringLit(_) => Set.empty

      case App(f, a)               => f.usedNames ++ a.usedNames
      case Lam(_, _, _, b)         => b.usedNames
      case Let(_, _, _, v, b)      => v.usedNames ++ b.usedNames
      case Fix(_, _, _, _, b, arg) => b.usedNames ++ arg.usedNames

      case Con(_, _, as)     => as.flatMap(_.usedNames).toSet
      case Field(_, _, s, i) => s.usedNames
      case Match(_, _, x, s, cs, o) =>
        s.usedNames ++ cs
          .flatMap(_._2.usedNames) ++ o.map(_.usedNames).getOrElse(Set.empty)

      case ReturnIO(v)           => v.usedNames
      case BindIO(_, _, x, v, b) => v.usedNames ++ b.usedNames

      case Foreign(_, _, as) => as.toSet.flatMap(_._1.usedNames)

    def maxName: LName = this match
      case Var(x, _)    => x
      case Global(_, _) => -1
      case IntLit(_)    => -1
      case BoolLit(_)   => -1
      case StringLit(_) => -1

      case App(f, a)               => f.maxName max a.maxName
      case Lam(x, _, _, b)         => x max b.maxName
      case Let(x, _, _, v, b)      => x max v.maxName max b.maxName
      case Fix(_, _, x, y, b, arg) => x max y max b.maxName max arg.maxName

      case Con(_, _, as)     => as.map(_.maxName).fold(-1)(_ max _)
      case Field(_, _, s, i) => s.maxName
      case Match(_, _, x, s, cs, o) =>
        x max s.maxName max cs.map(_._2.maxName).fold(-1)(_ max _) max o
          .map(_.maxName)
          .getOrElse(-1)

      case ReturnIO(v)           => v.maxName
      case BindIO(_, _, x, v, b) => v.maxName max b.maxName

      case Foreign(_, _, as) => as.map(_._1.maxName).fold(-1)(_ max _)

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
        case Var(x, _)    => sub.get(x).getOrElse(this)
        case Global(_, _) => this
        case IntLit(_)    => this
        case BoolLit(_)   => this
        case StringLit(_) => this

        case App(f, a) => App(f.subst(sub, scope), a.subst(sub, scope))
        case Lam(x0, t1, t2, b0) =>
          val (List((x, _)), b) =
            underN(List((x0, TDef(t1))), b0, sub, scope)
          Lam(x, t1, t2, b)
        case Fix(t1, t2, g0, x0, b0, arg) =>
          val (List((g, _), (x, _)), b) = underN(
            List((g0, TDef(t1, t2)), (x0, TDef(t1))),
            b0,
            sub,
            scope
          )
          Fix(t1, t2, g, x, b, arg.subst(sub, scope))
        case Let(x0, t, bt, v, b0) =>
          val (List((x, _)), b) = underN(List((x0, t)), b0, sub, scope)
          Let(x, t, bt, v.subst(sub, scope), b)

        case Con(x, cx, as) => Con(x, cx, as.map(_.subst(sub, scope)))
        case Field(dty, cx, s, i) =>
          Field(dty, cx, s.subst(sub, scope), i)
        case Match(dty, rty, x, scrut, cs, other) if scope.contains(x) =>
          val y = scope.max
          val nsub = sub + (x -> Var(y, TDef(TCon(dty))))
          val nscope = scope + y
          Match(
            dty,
            rty,
            y,
            scrut.subst(sub, scope),
            cs.map((x, t) => (x, t.subst(nsub, nscope))),
            other.map(_.subst(sub, scope))
          )
        case Match(dty, rty, x, scrut, cs, other) =>
          val nsub = sub - x
          val nscope = scope + x
          Match(
            dty,
            rty,
            x,
            scrut.subst(sub, scope),
            cs.map((x, t) => (x, t.subst(nsub, nscope))),
            other.map(_.subst(sub, scope))
          )

        case ReturnIO(v) => ReturnIO(v.subst(sub, scope))
        case BindIO(t1, t2, x0, v, b0) =>
          val (List((x, _)), b) = underN(List((x0, TDef(t1))), b0, sub, scope)
          BindIO(t1, t2, x, v.subst(sub, scope), b)

        case Foreign(rt, cmd, args) =>
          Foreign(rt, cmd, args.map((t, ty) => (t.subst(sub, scope), ty)))
  export Tm.*
