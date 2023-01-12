package core

import common.Common.*

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Ty, stage: Stage[Ty], value: Tm)

    override def toString: String = this match
      case DDef(x, t, S1, v)    => s"def $x : $t = $v"
      case DDef(x, t, S0(_), v) => s"def $x : $t := $v"
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
  enum Tm:
    case Var(ix: Ix)
    case Global(name: Name)
    case Prim(name: PrimName)
    case Let(name: Name, ty: Ty, stage: Stage[Ty], bty: Ty, value: Tm, body: Tm)
    case U(stage: Stage[Ty])

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, fnty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case FunTy(ty: Ty, vf: Ty, rt: Ty)
    case Fix(go: Name, name: Name, fnty: Ty, body: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm, ty: Ty)
    case Proj(tm: Tm, proj: ProjType, ty: Ty)
    case PairTy(fst: Ty, snd: Ty)

    case IntLit(value: Int)

    case Lift(vf: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Wk(tm: Tm)

    case Meta(id: MetaId)
    case AppPruning(tm: Tm, spine: Pruning)
    case Irrelevant

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
      case Var(x)                    => s"'$x"
      case Global(x)                 => s"$x"
      case Prim(x)                   => s"$x"
      case Let(x, t, S1, _, v, b)    => s"(let $x : $t = $v; $b)"
      case Let(x, t, S0(_), _, v, b) => s"(let $x : $t := $v; $b)"
      case U(S1)                     => "Meta"
      case U(S0(vf))                 => s"(Ty $vf)"

      case Pi(DontBind, Expl, t, b) => s"($t -> $b)"
      case Pi(x, i, t, b)           => s"(${i.wrap(s"$x : $t")} -> $b)"
      case Lam(x, Expl, _, b)       => s"(\\$x. $b)"
      case Lam(x, Impl, _, b)       => s"(\\{$x}. $b)"
      case App(f, a, Expl)          => s"($f $a)"
      case App(f, a, Impl)          => s"($f {$a})"
      case FunTy(a, _, b)           => s"($a -> $b)"
      case Fix(go, x, _, b, arg)    => s"(fix ($go $x. $b) $arg)"

      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case Sigma(x, t, b)        => s"(($x : $t) ** $b)"
      case Pair(a, b, _)         => s"($a, $b)"
      case Proj(t, p, _)         => s"$t$p"
      case PairTy(a, b)          => s"($a ** $b)"

      case IntLit(n) => s"$n"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Wk(t)      => s"(Wk $t)"
      case Irrelevant => "Ir"

      case Meta(id)          => s"?$id"
      case AppPruning(t, sp) => s"($t [${sp.reverse.mkString(", ")}])"
  export Tm.*
