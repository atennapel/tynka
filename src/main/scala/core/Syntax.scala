package core

import common.Common.*

object Syntax:
  type CStage = Stage[Tm]

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(name: Name, ty: Ty, stage: CStage, value: Tm)
    case DData(
        name: Name,
        ps: List[Name],
        cs: List[(Name, List[Ty])]
    )

    override def toString: String = this match
      case DDef(x, t, SMeta, v)  => s"def $x : $t = $v"
      case DDef(x, t, STy(_), v) => s"def $x : $t := $v"
      case DData(x, ps, Nil) =>
        s"data $x${if ps.isEmpty then "" else s" ${ps.mkString(" ")}"}"
      case DData(x, ps, cs) =>
        s"data $x${if ps.isEmpty then "" else s" ${ps.mkString(" ")}"} := ${cs
            .map((x, ts) => s"$x${if ts.isEmpty then "" else " "}${ts.mkString(" ")}")
            .mkString(" | ")}"
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
    case Lam(name: Bind, icit: Icit, fnty: Ty, body: Tm)
    case App(fn: Tm, arg: Tm, icit: Icit)
    case Fix(ty: Ty, rty: Ty, g: Bind, x: Bind, b: Tm, arg: Tm)

    case Sigma(name: Bind, ty: Ty, body: Ty)
    case Pair(fst: Tm, snd: Tm, ty: Ty)
    case Proj(tm: Tm, proj: ProjType, ty: Ty, pty: Ty)

    case Lift(cv: Ty, tm: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Foreign(rt: Ty, cmd: Tm, args: List[(Tm, Ty)])

    case TCon(name: Name, args: List[Ty])
    case Con(name: Name, con: Name, targs: List[Ty], args: List[Tm])
    case Match(
        dty: Ty,
        rty: Ty,
        scrut: Tm,
        cs: List[(Name, Int, Tm)],
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
      case TCon(name, args) => args.map(_.metas).foldLeft(Set.empty)(_ ++ _)
      case Con(name, con, targs, args) =>
        targs.map(_.metas).foldLeft(Set.empty[MetaId])(_ ++ _) ++ args
          .map(_.metas)
          .foldLeft(Set.empty[MetaId])(_ ++ _)
      case Match(dty, rty, scrut, cs, other) =>
        dty.metas ++ rty.metas ++ scrut.metas ++ cs
          .map((_, _, t) => t.metas)
          .foldLeft(Set.empty[MetaId])(_ ++ _) ++ other
          .map(_.metas)
          .getOrElse(Set.empty[MetaId])
      case Wk(tm)                => tm.metas
      case Meta(id)              => Set(id)
      case AppPruning(tm, spine) => tm.metas
      case Irrelevant            => Set.empty
      case Foreign(rt, cmd, args) =>
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

      case Foreign(rt, cmd, Nil) => s"(foreign $rt $cmd)"
      case Foreign(rt, cmd, as) =>
        s"(foreign $rt $cmd ${as.map(_._1).mkString(" ")})"

      case TCon(name, Nil)      => s"(tcon $name)"
      case TCon(name, as)       => s"(tcon $name ${as.mkString(" ")})"
      case Con(x, cx, Nil, Nil) => s"(con $x $cx)"
      case Con(x, cx, Nil, as)  => s"(con $x $cx ${as.mkString(" ")})"
      case Con(x, cx, tas, Nil) => s"(con $x $cx (${tas.mkString(" ")}))"
      case Con(x, cx, tas, as) =>
        s"(con $x $cx (${tas.mkString(" ")}) ${as.mkString(" ")})"

      case Match(_, _, scrut, cs, other) =>
        s"(match $scrut ${cs
            .map((c, _, b) => s"| $c $b")
            .mkString(" ")} ${other.map(t => s"| $t").getOrElse("")})"

      case Wk(t)      => s"(Wk $t)"
      case Irrelevant => "Ir"

      case Meta(id)          => s"?$id"
      case AppPruning(t, sp) => s"($t [${sp.reverse.mkString(", ")}])"
  export Tm.*

  object Fun:
    def apply(a: Ty, cv: Ty, b: Ty): Ty =
      App(App(App(Prim(PFun), a, Expl), cv, Impl), b, Expl)
    def unapply(value: Ty): Option[(Ty, Ty, Ty)] = value match
      case App(App(App(Prim(PFun), a, Expl), cv, Impl), b, Expl) =>
        Some((a, cv, b))
      case _ => None
