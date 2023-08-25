package surface

import common.Common.*
import scala.runtime.LazyVals.Names

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs
    def imports: List[String] =
      (
        defs.flatMap {
          case DImport(_, uri) => Some(uri)
          case _               => None
        }
      )

  enum Def:
    case DImport(pos: PosInfo, uri: String)
    case DDef(
        pos: PosInfo,
        opaque: Boolean,
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
      case DImport(pos, uri) => s"import \"$uri\""
      case DDef(_, opq, x, m, Some(t), v) =>
        s"${if opq then "opaque " else ""}def $x : $t ${if m then "" else ":"}= $v"
      case DDef(_, opq, x, m, None, v) =>
        s"${if opq then "opaque " else ""}def $x ${if m then "" else ":"}= $v"
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
    case Var(name: Name, rigid: Boolean = false)
    case Let(
        usage: Usage,
        name: Name,
        meta: Boolean,
        ty: Option[Ty],
        value: Tm,
        body: Tm
    )
    case U(stage: Stage[Ty])
    case Unfold(xs: List[Name], body: Tm)

    case IntLit(value: Int)
    case StringLit(value: String)

    case Pi(usage: Usage, name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)
    case Fix(g: Bind, x: Bind, b: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case Lift(ty: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Data(x: Bind, cs: List[(Name, List[(Bind, Ty)])])
    case Con(c: Name, t: Option[Ty], as: List[Tm])
    case Match(
        scrut: Tm,
        cs: List[(PosInfo, Name, Option[Name], List[Bind], Tm)],
        other: Option[(PosInfo, Tm)]
    )

    case Foreign(io: Boolean, rt: Ty, label: Tm, args: List[Tm])

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    def free: List[Name] = this match
      case Var(name, _) => List(name)
      case Let(_, name, meta, ty, value, body) =>
        ty.map(_.free).getOrElse(Nil) ++ value.free ++ body.free.filterNot(
          _ == name
        )
      case U(stage)     => Nil
      case Unfold(_, b) => b.free
      case Pi(_, name, icit, ty, body) =>
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
      case Data(x, cs) =>
        cs.flatMap((_, as) => as.flatMap((_, t) => t.free))
          .filterNot(_ == x.toName)
      case Con(_, t, as) => t.fold(Nil)(_.free) ++ as.flatMap(_.free)
      case Match(scrut, cs, other) =>
        scrut.free ++ cs
          .map((_, _, cx, ps, t) =>
            t.free.filterNot(x => ps.contains(DoBind(x)) && cx.exists(_ == x))
          )
          .foldLeft(List.empty[Name])((acc, xs) => acc ++ xs) ++ other
          .map((_, t) => t.free)
          .getOrElse(Nil)
      case Foreign(_, rt, label, args) =>
        rt.free ++ label.free ++ args
          .map(_.free)
          .flatten
      case Hole(name)   => Nil
      case Pos(pos, tm) => tm.free
      case IntLit(_)    => Nil
      case StringLit(_) => Nil

    override def toString: String = this match
      case Var(x, true) => s"rigid $x"
      case Var(x, _)    => s"$x"
      case Let(u, x, m, None, v, b) =>
        s"(let ${u.prefix}$x ${if m then "" else ":"}= $v; $b)"
      case Let(u, x, m, Some(t), v, b) =>
        s"(let ${u.prefix}$x : $t ${if m then "" else ":"}= $v; $b)"
      case U(s)          => s"$s"
      case Unfold(xs, b) => s"(unfold ${xs.mkString(" ")}; $b)"

      case IntLit(v)    => s"$v"
      case StringLit(v) => s"\"$v\""

      case Pi(Many, DontBind, Expl, t, b) => s"($t -> $b)"
      case Pi(u, x, i, t, b) => s"(${i.wrap(s"${u.prefix}$x : $t")} -> $b)"
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

      case Data(x, Nil) => s"(data $x.)"
      case Data(x, as) =>
        s"(data $x. ${as.map((c, as) => s"$c ${as.map((x, t) => s"($x : $t)").mkString(" ")}").mkString(" | ")})"
      case Con(c, None, Nil)    => s"(con $c)"
      case Con(c, None, as)     => s"(con $c ${as.mkString(" ")})"
      case Con(c, Some(t), Nil) => s"(con $c {$t})"
      case Con(c, Some(t), as)  => s"(con $c {$t} ${as.mkString(" ")})"
      case Match(scrut, cs, other) =>
        s"(match $scrut ${cs
            .map((_, c, cx, ps, b) =>
              s"| $c${cx match { case None => ""; case Some(x) => s" {$x}" }} ${ps.mkString(" ")}. $b"
            )
            .mkString(" ")} ${other.map((_, t) => s"|. $t").getOrElse("")})"

      case Hole(None)    => "_"
      case Hole(Some(x)) => s"_$x"

      case Pos(_, t) => s"$t"
  export Tm.*
