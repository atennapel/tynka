package core

import common.Common.*

object Syntax:
  type CStage = Stage[Tm]

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Ty, stage: CStage, value: Tm)

    override def toString: String = this match
      case DDef(x, t, SMeta, v)  => s"def $x : $t = $v"
      case DDef(x, t, STy(_), v) => s"def $x : $t := $v"
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
    case Let(
        usage: Usage,
        name: Name,
        ty: Ty,
        stage: CStage,
        bty: Ty,
        value: Tm,
        body: Tm
    )
    case U(stage: CStage)

    case IntLit(value: Int)
    case StringLit(value: String)

    case Pi(usage: Usage, name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Fun(usage: Usage, pty: Ty, cv: Ty, rty: Ty)
    case Lam(name: Bind, icit: Icit, fnty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Fix(ty: Ty, rty: Ty, g: Bind, x: Bind, b: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm, ty: Ty)
    case Proj(tm: Tm, proj: ProjType, ty: Ty, pty: Ty)

    case Lift(cv: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Foreign(io: Boolean, rt: Ty, cmd: Tm, args: List[(Tm, Ty)])

    case Data(x: Bind, cs: List[(Name, List[(Bind, Ty)])])
    case Con(c: Name, t: Ty, as: List[Tm])
    case Match(
        dty: Ty,
        rty: Ty,
        scrut: Tm,
        cs: List[(Name, Boolean, Int, Tm)],
        other: Option[Tm]
    )

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

    def metas: Set[MetaId] = this match
      case Var(ix)      => Set.empty
      case Global(name) => Set.empty
      case Prim(name)   => Set.empty
      case IntLit(_)    => Set.empty
      case StringLit(_) => Set.empty
      case U(stage)     => stage.fold(Set.empty, _.metas)
      case Let(_, name, ty, stage, bty, value, body) =>
        ty.metas ++ stage.fold(
          Set.empty,
          _.metas
        ) ++ bty.metas ++ value.metas ++ body.metas
      case Pi(_, name, icit, ty, body) => ty.metas ++ body.metas
      case Fun(_, a, b, c)             => a.metas ++ b.metas ++ c.metas
      case Lam(name, icit, fnty, body) => fnty.metas ++ body.metas
      case App(fn, arg, icit)          => fn.metas ++ arg.metas
      case Fix(ty, rty, g, x, b, arg) =>
        ty.metas ++ rty.metas ++ b.metas ++ arg.metas
      case Sigma(name, ty, body)   => ty.metas ++ body.metas
      case Pair(fst, snd, ty)      => fst.metas ++ snd.metas ++ ty.metas
      case Proj(tm, proj, ty, pty) => tm.metas ++ ty.metas ++ pty.metas
      case Lift(cv, tm)            => cv.metas ++ tm.metas
      case Quote(tm)               => tm.metas
      case Splice(tm)              => tm.metas
      case Data(_, cs) =>
        cs.flatMap((_, as) => as.flatMap((_, t) => t.metas)).toSet
      case Con(con, ty, args) => ty.metas ++ args.flatMap(_.metas)
      case Match(dty, rty, scrut, cs, other) =>
        dty.metas ++ rty.metas ++ scrut.metas ++ cs
          .map((_, _, _, t) => t.metas)
          .foldLeft(Set.empty[MetaId])(_ ++ _) ++ other
          .map(_.metas)
          .getOrElse(Set.empty[MetaId])
      case Wk(tm)                => tm.metas
      case Meta(id)              => Set(id)
      case AppPruning(tm, spine) => tm.metas
      case Irrelevant            => Set.empty
      case Foreign(_, rt, cmd, args) =>
        rt.metas ++ cmd.metas ++ args
          .map((a, b) => a.metas ++ b.metas)
          .foldLeft(Set.empty[MetaId])(_ ++ _)

    override def toString: String = this match
      case Var(x)                       => s"'$x"
      case Global(x)                    => s"$x"
      case Prim(x)                      => s"$x"
      case Let(u, x, t, SMeta, _, v, b) => s"(let ${u.prefix}$x : $t = $v; $b)"
      case Let(u, x, t, STy(_), _, v, b) =>
        s"(let ${u.prefix}$x : $t := $v; $b)"
      case U(s) => s"$s"

      case IntLit(v)    => s"$v"
      case StringLit(v) => s"\"$v\""

      case Pi(Many, DontBind, Expl, t, b) => s"($t -> $b)"
      case Pi(u, x, i, t, b)  => s"(${i.wrap(s"${u.prefix}$x : $t")} -> $b)"
      case Fun(Many, a, _, b) => s"($a -> $b)"
      case Fun(u, a, _, b)    => s"($a ${u.prefix}-> $b)"
      case Lam(x, Expl, _, b) => s"(\\$x. $b)"
      case Lam(x, Impl, _, b) => s"(\\{$x}. $b)"
      case App(f, a, Expl)    => s"($f $a)"
      case App(f, a, Impl)    => s"($f {$a})"
      case Fix(_, _, g, x, b, arg) => s"(fix ($g $x. $b) $arg)"

      case Sigma(DontBind, t, b) => s"($t ** $b)"
      case Sigma(x, t, b)        => s"(($x : $t) ** $b)"
      case Pair(a, b, _)         => s"($a, $b)"
      case Proj(t, p, _, _)      => s"$t$p"

      case Lift(_, t) => s"^$t"
      case Quote(t)   => s"`$t"
      case Splice(t)  => s"$$$t"

      case Foreign(io, rt, cmd, Nil) =>
        s"(foreign${if io then "IO" else ""} $rt $cmd)"
      case Foreign(io, rt, cmd, as) =>
        s"(foreign${if io then "IO" else ""} $rt $cmd ${as.map(_._1).mkString(" ")})"

      case Data(x, Nil) => s"(data $x.)"
      case Data(x, as) =>
        s"(data $x. ${as.map((c, as) => s"$c ${as.map((x, t) => s"($x : $t)").mkString(" ")}").mkString(" | ")})"
      case Con(c, t, Nil) => s"(con $c {$t})"
      case Con(c, t, as)  => s"(con $c {$t} ${as.mkString(" ")})"

      case Match(_, _, scrut, cs, other) =>
        s"(match $scrut ${cs
            .map((c, _, _, b) => s"| $c $b")
            .mkString(" ")} ${other.map(t => s"| $t").getOrElse("")})"

      case Wk(t)      => s"(Wk $t)"
      case Irrelevant => "Ir"

      case Meta(id)          => s"?$id"
      case AppPruning(t, sp) => s"($t [${sp.reverse.mkString(", ")}])"
  export Tm.*
