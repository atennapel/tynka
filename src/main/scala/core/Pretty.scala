package core

import common.Common.*
import Syntax.*

import scala.annotation.tailrec

object Pretty:
  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(f, a, Expl) => s"${prettyApp(f)} ${prettyParen(a)}"
    case App(f, a, Impl) => s"${prettyApp(f)} {${pretty(a)}}"
    case f               => prettyParen(f)

  private def prettySigma(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Sigma(DontBind, t, b) =>
      s"${prettyParen(t, true)} ** ${prettySigma(b)(DontBind.toName :: ns)}"
    case Sigma(DoBind(x0), t, b) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) ** ${prettySigma(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Pi(DontBind, Expl, t, b) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(DoBind(x0), Expl, t, b) =>
      val x = x0.fresh
      s"($x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case Pi(x0, Impl, t, b) =>
      val x = x0.fresh
      s"{$x : ${pretty(t)}} -> ${prettyPi(b)(x.toName :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(implicit ns: List[Name]): String =
    def go(tm: Tm, first: Boolean = false)(implicit ns: List[Name]): String =
      tm match
        case Lam(x0, Expl, _, b) =>
          val x = x0.fresh
          s"${if first then "" else " "}$x${go(b)(x.toName :: ns)}"
        case Lam(x0, Impl, _, b) =>
          val x = x0.fresh
          s"${if first then "" else " "}{$x}${go(b)(x.toName :: ns)}"
        case rest => s". ${pretty(rest)}"
    s"\\${go(tm, true)}"

  @tailrec
  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String =
    tm match
      case Var(_)              => pretty(tm)
      case Global(_, _)        => pretty(tm)
      case Prim(_)             => pretty(tm)
      case Pair(_, _, _)       => pretty(tm)
      case Proj(_, _, _, _)    => pretty(tm)
      case Meta(_)             => pretty(tm)
      case Lift(_, _)          => pretty(tm)
      case Quote(_)            => pretty(tm)
      case Splice(_)           => pretty(tm)
      case AppPruning(_, _)    => pretty(tm)
      case App(_, _, _) if app => pretty(tm)
      case U(_)                => pretty(tm)
      case IntLit(_)           => pretty(tm)
      case Irrelevant          => pretty(tm)
      case StringLit(_)        => pretty(tm)
      case Wk(tm)              => prettyParen(tm, app)(ns.tail)
      case _                   => s"(${pretty(tm)})"

  private def flattenPair(tm: Tm): List[Tm] = tm match
    case Pair(fst, snd, _) => fst :: flattenPair(snd)
    case tm                => List(tm)

  private def prettyLift(x: Name, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x :: ns)

  def pretty(s: CStage)(implicit ns: List[Name]): String = s"${s.map(pretty)}"

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Var(ix)      => s"${ns(ix.expose)}"
    case Global(m, x) => s"$m:$x"
    case Prim(x)      => s"$x"
    case Let(x0, t, s, _, v, b) =>
      val x = x0.fresh
      val ss = s match
        case SMeta  => ""
        case STy(_) => ":"
      s"let $x : ${pretty(t)} $ss= ${pretty(v)}; ${prettyLift(x, b)}"
    case U(s) => pretty(s)

    case Pi(_, _, _, _)  => prettyPi(tm)
    case Lam(_, _, _, _) => prettyLam(tm)
    case App(_, _, _)    => prettyApp(tm)

    case Fix(_, _, g0, x0, b, arg) =>
      val g = g0.fresh
      val x = x0.fresh
      s"fix ($g $x. ${prettyParen(b)(x.toName :: g.toName :: ns)}) ${prettyParen(arg)}"

    case Sigma(_, _, _) => prettySigma(tm)
    case Pair(_, _, _) =>
      val es = flattenPair(tm)
      if es.last == Prim(PUnit) then s"[${es.init.map(pretty).mkString(", ")}]"
      else s"(${es.map(pretty).mkString(", ")})"
    case Proj(t, p, _, _) => s"${prettyParen(t)}$p"
    case TPair(a, b)      => s"TPair ${prettyParen(a)} ${prettyParen(b)}"

    case IntLit(n)    => s"$n"
    case StringLit(v) => s"\"$v\""

    case TCon(x0, Nil) =>
      val x = x0.fresh
      s"tcon $x."
    case TCon(x0, cs) =>
      val x = x0.fresh
      s"tcon $x. ${cs.map(as => s"(${as.map(a => prettyParen(a)(x.toName :: ns)).mkString(" ")})").mkString(" ")}"
    case Con(ty, i, Nil) => s"con ${prettyParen(ty)} #$i"
    case Con(ty, i, as) =>
      s"con ${prettyParen(ty)} #$i ${as.map(a => prettyParen(a)).mkString(" ")}"
    case Case(ty, _, s, Nil) => s"case ${prettyParen(ty)} ${prettyParen(s)}"
    case Case(ty, _, s, cs) =>
      s"case ${prettyParen(ty)} ${prettyParen(s)} ${cs.map(a => prettyParen(a)).mkString(" ")}"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case Foreign(rt, cmd, Nil) =>
      s"foreign ${prettyParen(rt)} ${prettyParen(cmd)}"
    case Foreign(rt, cmd, as) =>
      s"foreign ${prettyParen(rt)} ${prettyParen(cmd)} ${as.map((a, _) => prettyParen(a)).mkString(" ")}"

    case Wk(tm)     => pretty(tm)(ns.tail)
    case Irrelevant => "Ir"

    case Meta(id)         => s"?$id"
    case AppPruning(f, _) => s"?*${prettyParen(f)}"

  def pretty(d: Def): String = d match
    case DDef(m, x, t, SMeta, v) =>
      s"def $m:$x : ${pretty(t)(Nil)} = ${pretty(v)(Nil)}"
    case DDef(m, x, t, STy(_), v) =>
      s"def $m:$x : ${pretty(t)(Nil)} := ${pretty(v)(Nil)}"

  def pretty(ds: Defs): String = ds.toList.map(pretty).mkString("\n")
