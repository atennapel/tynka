package surface

import common.Common.*

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Option[Ty], value: Tm)

    override def toString: String = this match
      case DDef(x, Some(t), v) => s"def $x : $t = $v"
      case DDef(x, None, v)    => s"def $x = $v"
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
    case Let(name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Type

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    override def toString: String = this match
      case Var(x)                => s"$x"
      case Let(x, None, v, b)    => s"(let $x = $v; $b)"
      case Let(x, Some(t), v, b) => s"(let $x : $t = $v; $b)"
      case Type                  => "Type"

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

      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case Sigma(x, t, b)        => s"(($x : $t) ** $b)"
      case Pair(a, b)            => s"($a, $b)"
      case Proj(t, p)            => s"$t$p"

      case Hole(None)    => "_"
      case Hole(Some(x)) => s"_$x"

      case Pos(_, t) => s"$t"
  export Tm.*
