package core

import common.Common.*

object Syntax:
  type CStage = Stage[Tm]

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(module: String, name: Name, ty: Ty, stage: CStage, value: Tm)

    override def toString: String = this match
      case DDef(m, x, t, SMeta, v)  => s"def $m:$x : $t = $v"
      case DDef(m, x, t, STy(_), v) => s"def $m:$x : $t := $v"
  export Def.*

  type Ty = Tm
  enum Tm:
    case Var(ix: Ix)
    case Global(module: String, name: Name)
    case Let(name: Name, ty: Ty, stage: CStage, bty: Ty, value: Tm, body: Tm)
    case U(stage: CStage)

    case VF
    case VFVal
    case VFFun

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case TFun(pty: Ty, vf: Ty, rty: Ty)
    case Lam(name: Bind, icit: Icit, fnty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Fix(ty: Ty, rty: Ty, g: Bind, x: Bind, b: Tm, arg: Tm)

    case Lift(vf: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case TInt
    case IntLit(n: Int)

    case TCon(name: Bind, cons: List[(Name, List[Ty])])

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
      case Var(x)                     => s"'$x"
      case Global(m, x)               => s"$m:$x"
      case Let(x, t, SMeta, _, v, b)  => s"(let $x : $t = $v; $b)"
      case Let(x, t, STy(_), _, v, b) => s"(let $x : $t := $v; $b)"
      case U(s)                       => s"$s"

      case VF    => "VF"
      case VFVal => "Val"
      case VFFun => "Fun"

      case Pi(DontBind, Expl, t, b) => s"($t -> $b)"
      case Pi(x, i, t, b)           => s"(${i.wrap(s"$x : $t")} -> $b)"
      case TFun(a, _, b)            => s"($a -> $b)"
      case Lam(x, Expl, _, b)       => s"(\\$x. $b)"
      case Lam(x, Impl, _, b)       => s"(\\{$x}. $b)"
      case App(f, a, Expl)          => s"($f $a)"
      case App(f, a, Impl)          => s"($f {$a})"
      case Fix(_, _, g, x, b, arg)  => s"(fix ($g $x. $b) $arg)"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case TInt      => "Int"
      case IntLit(n) => s"$n"

      case TCon(x, cs) =>
        s"tcon $x. ${cs.map((x, as) => s"$x${if as.isEmpty then "" else " "}${as.mkString(" ")}").mkString(" | ")}"

      case Wk(t)      => s"(Wk $t)"
      case Irrelevant => "Ir"

      case Meta(id)          => s"?$id"
      case AppPruning(t, sp) => s"($t [${sp.reverse.mkString(", ")}])"
  export Tm.*
