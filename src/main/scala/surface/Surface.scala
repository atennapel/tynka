package surface

import common.Common.*

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, meta: Boolean, ty: Option[Ty], value: Tm)

    override def toString: String = this match
      case DDef(x, m, Some(t), v) => s"def $x : $t ${if m then "" else ":"}= $v"
      case DDef(x, m, None, v)    => s"def $x ${if m then "" else ":"}= $v"
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
    case U(stage: Stage[Tm])

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case IntLit(value: Int)

    case TCon(name: Bind, cons: List[List[Ty]])
    case Con(ix: Int, args: List[Tm])

    case Lift(ty: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    override def toString: String = this match
      case Var(x)                => s"$x"
      case Let(x, m, None, v, b) => s"(let $x ${if m then "" else ":"}= $v; $b)"
      case Let(x, m, Some(t), v, b) =>
        s"(let $x : $t ${if m then "" else ":"}= $v; $b)"
      case U(s) => s"$s"

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

      case IntLit(n) => s"$n"

      case TCon(x, Nil) => s"(tcon $x.)"
      case TCon(x, cs) =>
        s"(tcon $x. ${cs.map(as => s"(${as.mkString(" ")})").mkString(" ")})"
      case Con(i, Nil) => s"(con #$i)"
      case Con(i, as)  => s"(con #$i ${as.mkString(" ")})"

      case Lift(t)   => s"^$t"
      case Quote(t)  => s"`$t"
      case Splice(t) => s"$$$t"

      case Hole(None)    => "_"
      case Hole(Some(x)) => s"_$x"

      case Pos(_, t) => s"$t"
  export Tm.*
