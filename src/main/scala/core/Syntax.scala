package core

import common.Common.*

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Ty, value: Tm)

    override def toString: String = this match
      case DDef(x, t, v) => s"def $x : $t = $v"
  export Def.*

  enum ProjType:
    case Fst
    case Snd
    case Named(name: Option[Name], ix: Int)

    override def toString: String = this match
      case Fst               => ".1"
      case Snd               => ".2"
      case Named(Some(x), _) => s".$x"
      case Named(None, i)    => s".$i"
  export ProjType.*

  type Ty = Tm
  type Univ = Tm
  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name)
    case Prim(name: PrimName)
    case Let(name: Name, ty: Ty, value: Tm, body: Tm)

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm)
    case Proj(tm: Tm, proj: ProjType)

    case Lift(vf: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Wk(tm: Tm)

    case Meta(id: MetaId)
    case AppPruning(tm: Tm, spine: Pruning)

    def appPruning(pr: Pruning): Tm =
      def go(x: Ix, pr: Pruning): Tm = pr match
        case Nil           => this
        case Some(i) :: pr => App(go(x + 1, pr), Var(x), i)
        case None :: pr    => go(x + 1, pr)
      go(ix0, pr)

    def quote: Tm = this match
      case Splice(t) => t
      case t         => Quote(t)
    def splice: Tm = this match
      case Quote(t) => t
      case t        => Splice(t)

    override def toString: String = this match
      case Var(x)          => s"'$x"
      case Global(x)       => s"$x"
      case Prim(x)         => s"$x"
      case Let(x, t, v, b) => s"(let $x : $t = $v; $b)"

      case Pi(DontBind, Expl, t, b) => s"($t -> $b)"
      case Pi(x, i, t, b)           => s"(${i.wrap(s"$x : $t")} -> $b)"
      case Lam(x, Expl, b)          => s"(\\$x. $b)"
      case Lam(x, Impl, b)          => s"(\\{$x}. $b)"
      case App(f, a, Expl)          => s"($f $a)"
      case App(f, a, Impl)          => s"($f {$a})"

      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case Sigma(x, t, b)        => s"(($x : $t) ** $b)"
      case Pair(a, b)            => s"($a, $b)"
      case Proj(t, p)            => s"$t$p"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Wk(t) => s"(Wk $t)"

      case Meta(id)          => s"?$id"
      case AppPruning(t, sp) => s"($t [${sp.reverse.mkString(", ")}])"
  export Tm.*
