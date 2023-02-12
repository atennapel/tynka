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
    case Global(module: String, name: Name)
    case Prim(name: PrimName)
    case Let(name: Name, ty: Ty, stage: CStage, bty: Ty, value: Tm, body: Tm)
    case U(stage: CStage)

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, fnty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Fix(ty: Ty, rty: Ty, g: Bind, x: Bind, b: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case TPair(fst: Ty, snd: Ty)
    case Pair(fst: Tm, snd: Tm, ty: Ty)
    case Proj(tm: Tm, proj: ProjType, ty: Ty, pty: Ty)

    case IntLit(value: Int)
    case StringLit(value: String)

    case TCon(name: Bind, cons: List[List[Ty]])
    case Con(ty: Ty, ix: Int, args: List[Tm])
    case Case(ty: Ty, rty: Ty, scrut: Tm, cs: List[Tm])

    case Lift(vf: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Foreign(rt: Ty, cmd: Tm, args: List[(Tm, Ty)])

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

    def box(t: Ty): Tm = App(App(Prim(PBox), t, Impl), this, Expl)
    def unbox(t: Ty): Tm = App(App(Prim(PUnbox), t, Impl), this, Expl)

    override def toString: String = this match
      case Var(x)                     => s"'$x"
      case Global(m, x)               => s"$m:$x"
      case Prim(x)                    => s"$x"
      case Let(x, t, SMeta, _, v, b)  => s"(let $x : $t = $v; $b)"
      case Let(x, t, STy(_), _, v, b) => s"(let $x : $t := $v; $b)"
      case U(s)                       => s"$s"

      case Pi(DontBind, Expl, t, b) => s"($t -> $b)"
      case Pi(x, i, t, b)           => s"(${i.wrap(s"$x : $t")} -> $b)"
      case Lam(x, Expl, _, b)       => s"(\\$x. $b)"
      case Lam(x, Impl, _, b)       => s"(\\{$x}. $b)"
      case App(f, a, Expl)          => s"($f $a)"
      case App(f, a, Impl)          => s"($f {$a})"
      case Fix(_, _, g, x, b, arg)  => s"(fix ($g $x. $b) $arg)"

      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case TPair(fst, snd)       => s"(TPair $fst $snd)"
      case Sigma(x, t, b)        => s"(($x : $t) ** $b)"
      case Pair(a, b, _)         => s"($a, $b)"
      case Proj(t, p, _, _)      => s"$t$p"

      case IntLit(n)    => s"$n"
      case StringLit(v) => s"\"$v\""

      case TCon(x, Nil) => s"(tcon $x.)"
      case TCon(x, cs) =>
        s"(tcon $x. ${cs.map(as => s"(${as.mkString(" ")})").mkString(" ")})"
      case Con(ty, i, Nil)     => s"(con $ty #$i)"
      case Con(ty, i, as)      => s"(con $ty #$i ${as.mkString(" ")})"
      case Case(ty, _, s, Nil) => s"(case $ty $s)"
      case Case(ty, _, s, cs)  => s"(case $ty $s ${cs.mkString(" ")})"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Foreign(rt, cmd, Nil) => s"(foreign $rt $cmd)"
      case Foreign(rt, cmd, as) =>
        s"(foreign $rt $cmd ${as.map(_._1).mkString(" ")})"

      case Wk(t)      => s"(Wk $t)"
      case Irrelevant => "Ir"

      case Meta(id)          => s"?$id"
      case AppPruning(t, sp) => s"($t [${sp.reverse.mkString(", ")}])"
  export Tm.*

  def tfun(a: Ty, vf: Ty, b: Ty): Ty =
    App(App(App(Prim(PTFun), a, Expl), vf, Impl), b, Expl)
