package surface

import common.Common.*

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case DDef(
        pos: PosInfo,
        name: Name,
        meta: Boolean,
        ty: Option[Ty],
        value: Tm
    )
    case DData(
        pos: PosInfo,
        name: Name,
        ps: List[Name],
        cs: List[(PosInfo, Name, List[Ty])]
    )

    override def toString: String = this match
      case DDef(_, x, m, Some(t), v) =>
        s"def $x : $t ${if m then "" else ":"}= $v"
      case DDef(_, x, m, None, v) => s"def $x ${if m then "" else ":"}= $v"
      case DData(_, x, ps, Nil) =>
        s"data $x${if ps.isEmpty then "" else s" ${ps.mkString(" ")}"}"
      case DData(_, x, ps, cs) =>
        s"data $x${if ps.isEmpty then "" else s" ${ps.mkString(" ")}"} := ${cs
            .map((_, x, ts) => s"$x${if ts.isEmpty then "" else " "}${ts.mkString(" ")}")
            .mkString(" | ")}"
  export Def.*

  enum ArgInfo:
    case ArgNamed(name: Name)
    case ArgIcit(icit: Icit)
  export ArgInfo.*

  enum ProjType:
    case Fst
    case Snd
    case Named(name: Name)

    override def toString: String = this match
      case Fst      => ".1"
      case Snd      => ".2"
      case Named(x) => s".$x"
  export ProjType.*

  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(name: Name, meta: Boolean, ty: Option[Ty], value: Tm, body: Tm)
    case U(stage: Stage[Ty])

    case IntLit(value: Int)
    case StringLit(value: String)

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)
    case Fix(g: Bind, x: Bind, b: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case Lift(ty: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Match(
        scrut: Tm,
        cs: List[(PosInfo, Name, List[Bind], Tm)],
        other: Option[(PosInfo, Tm)]
    )

    case Foreign(io: Boolean, rt: Ty, label: Tm, args: List[Tm])

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    def free: List[Name] = this match
      case Var(name) => List(name)
      case Let(name, meta, ty, value, body) =>
        ty.map(_.free).getOrElse(Nil) ++ value.free ++ body.free.filterNot(
          _ == name
        )
      case U(stage) => Nil
      case Pi(name, icit, ty, body) =>
        ty.free ++ body.free.filterNot(_ == name.toName)
      case Lam(name, info, ty, body) =>
        ty.map(_.free).getOrElse(Nil) ++ body.free.filterNot(_ == name.toName)
      case App(fn, arg, info) => fn.free ++ arg.free
      case Fix(g, x, b, arg) =>
        b.free.filterNot(y => y == g.toName || y == x.toName) ++ arg.free
      case Sigma(name, ty, body) =>
        ty.free ++ body.free.filterNot(_ == name.toName)
      case Pair(fst, snd) => fst.free ++ snd.free
      case Proj(tm, proj) => tm.free
      case Lift(ty)       => ty.free
      case Quote(tm)      => tm.free
      case Splice(tm)     => tm.free
      case Match(scrut, cs, other) =>
        scrut.free ++ cs
          .map((_, _, ps, t) => t.free.filterNot(x => ps.contains(DoBind(x))))
          .foldLeft(List.empty[Name])((acc, xs) => acc ++ xs) ++ other
          .map((_, t) => t.free)
          .getOrElse(Nil)
      case Foreign(_, rt, label, args) =>
        rt.free ++ label.free ++ args
          .map(_.free)
          .foldLeft(List.empty[Name])(_ ++ _)
      case Hole(name)   => Nil
      case Pos(pos, tm) => tm.free
      case IntLit(_)    => Nil
      case StringLit(_) => Nil

    override def toString: String = this match
      case Var(x)                => s"$x"
      case Let(x, m, None, v, b) => s"(let $x ${if m then "" else ":"}= $v; $b)"
      case Let(x, m, Some(t), v, b) =>
        s"(let $x : $t ${if m then "" else ":"}= $v; $b)"
      case U(s) => s"$s"

      case IntLit(v)    => s"$v"
      case StringLit(v) => s"\"$v\""

      case Pi(DontBind, Expl, t, b)        => s"($t -> $b)"
      case Pi(x, i, t, b)                  => s"(${i.wrap(s"$x : $t")} -> $b)"
      case Lam(x, ArgNamed(y), None, b)    => s"(\\{$x = $y}. $b)"
      case Lam(x, ArgNamed(y), Some(t), b) => s"(\\{$x : $t = $y}. $b)"
      case Lam(x, ArgIcit(Expl), None, b)  => s"(\\$x. $b)"
      case Lam(x, ArgIcit(Impl), None, b)  => s"(\\{$x}. $b)"
      case Lam(x, ArgIcit(i), Some(t), b)  => s"(\\${i.wrap(s"$x : $t")}. $b)"
      case App(f, a, ArgNamed(x))          => s"($f {$x = $a})"
      case App(f, a, ArgIcit(Expl))        => s"($f $a)"
      case App(f, a, ArgIcit(Impl))        => s"($f {$a})"
      case Fix(g, x, b, arg)               => s"(fix ($g $x. $b) $arg)"

      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case Sigma(x, t, b)        => s"(($x : $t) ** $b)"
      case Pair(a, b)            => s"($a, $b)"
      case Proj(t, p)            => s"$t$p"

      case Lift(t)   => s"^$t"
      case Quote(t)  => s"`$t"
      case Splice(t) => s"$$$t"

      case Foreign(false, rt, l, Nil) => s"(foreign $rt $l)"
      case Foreign(false, rt, l, as)  => s"(foreign $rt $l ${as.mkString(" ")})"
      case Foreign(true, rt, l, Nil)  => s"(foreignIO $rt $l)"
      case Foreign(true, rt, l, as) => s"(foreignIO $rt $l ${as.mkString(" ")})"

      case Match(scrut, cs, other) =>
        s"(match $scrut ${cs
            .map((_, c, ps, b) => s"| $c ${ps.mkString(" ")}. $b")
            .mkString(" ")} ${other.map((_, t) => s"|. $t").getOrElse("")})"

      case Hole(None)    => "_"
      case Hole(Some(x)) => s"_$x"

      case Pos(_, t) => s"$t"
  export Tm.*
