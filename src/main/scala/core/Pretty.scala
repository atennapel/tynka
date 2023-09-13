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
    case Sigma(DoBind(x), t, b) =>
      s"($x : ${pretty(t)}) ** ${prettySigma(b)(x :: ns)}"
    case rest => pretty(rest)

  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Fun(Many, a, _, b) => s"${prettyParen(a, true)} -> ${prettyPi(b)}"
    case Fun(u, a, _, b) =>
      s"${prettyParen(a, true)} ${u.prefix}-> ${prettyPi(b)}"
    case Pi(Many, DontBind, PiExpl, t, b) =>
      s"${prettyParen(t, true)} -> ${prettyPi(b)(DontBind.toName :: ns)}"
    case Pi(u, DoBind(x), PiExpl, t, b) =>
      s"(${u.prefix}$x : ${pretty(t)}) -> ${prettyPi(b)(x :: ns)}"
    case Pi(u, x, i, t, b) =>
      s"${i.wrap(s"${u.prefix}$x : ${pretty(t)}")} -> ${prettyPi(b)(x.toName :: ns)}"
    case rest => pretty(rest)

  private def prettyLam(tm: Tm)(implicit ns: List[Name]): String =
    def go(tm: Tm, first: Boolean = false)(implicit ns: List[Name]): String =
      tm match
        case Lam(x, Expl, _, b) =>
          s"${if first then "" else " "}$x${go(b)(x.toName :: ns)}"
        case Lam(x, Impl, _, b) =>
          s"${if first then "" else " "}{$x}${go(b)(x.toName :: ns)}"
        case rest => s". ${pretty(rest)}"
    s"\\${go(tm, true)}"

  @tailrec
  private def prettyParen(tm: Tm, app: Boolean = false)(implicit
      ns: List[Name]
  ): String =
    tm match
      case Var(_)              => pretty(tm)
      case IntLit(_)           => pretty(tm)
      case StringLit(_)        => pretty(tm)
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
      case Irrelevant          => pretty(tm)
      case Wk(tm)              => prettyParen(tm, app)(ns.tail)
      case _                   => s"(${pretty(tm)})"

  private def flattenPair(tm: Tm): List[Tm] = tm match
    case Pair(fst, snd, _) => fst :: flattenPair(snd)
    case tm                => List(tm)

  private def prettyLift(x: Name, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x :: ns)

  def pretty(s: CStage)(implicit ns: List[Name]): String = s"${s.map(pretty)}"

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Var(ix) =>
      val x = ns(ix.expose)
      if ns.take(ix.expose).contains(x) then
        s"${ns(ix.expose)}@${ns.size - ix.expose - 1}"
      else s"$x"
    case Global(m, x) => s"$m/$x"
    case Prim(x)      => s"$x"
    case IntLit(x)    => s"$x"
    case StringLit(x) => s"\"$x\""
    case Let(u, x, t, s, _, v, b) =>
      val ss = s match
        case SMeta  => ""
        case STy(_) => ":"
      s"let ${u.prefix}$x : ${pretty(t)} $ss= ${pretty(v)}; ${prettyLift(x, b)}"
    case U(s) => pretty(s)

    case Pi(_, _, _, _, _) => prettyPi(tm)
    case Fun(_, _, _, _)   => prettyPi(tm)
    case Lam(_, _, _, _)   => prettyLam(tm)
    case App(_, _, _)      => prettyApp(tm)

    case Fix(_, _, g, x, b, arg) =>
      s"fix ($g $x. ${prettyParen(b)(x.toName :: g.toName :: ns)}) ${prettyParen(arg)}"

    case Sigma(_, _, _) => prettySigma(tm)
    case Pair(_, _, _) =>
      val es = flattenPair(tm)
      if es.last == Prim(PUnit) then s"[${es.init.map(pretty).mkString(", ")}]"
      else s"(${es.map(pretty).mkString(", ")})"
    case Proj(t, p, _, _) => s"${prettyParen(t)}$p"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case Data(x, Nil) => s"data $x."
    case Data(x, as) =>
      s"data $x. ${as.map((c, as) => s"$c ${as.map((x, t) => s"($x : $t)").mkString(" ")}").mkString(" | ")}"
    case Con(c, t, Nil) => s"con $c {$t}"
    case Con(c, t, as)  => s"con $c {$t} ${as.mkString(" ")}"

    case Match(_, _, scrut, cs, other) =>
      s"match ${prettyParen(scrut, true)} ${cs
          .map((c, _, _, b) => s"| $c ${pretty(b)}")
          .mkString(" ")}${if other.isDefined then " " else ""}${other
          .map(t => s"| ${pretty(t)}")
          .getOrElse("")}"

    case Foreign(io, rt, cmd, Nil) =>
      s"foreign${if io then "IO" else ""} ${prettyParen(rt)} ${prettyParen(cmd)}"
    case Foreign(io, rt, cmd, as) =>
      s"foreign${if io then "IO" else ""} ${prettyParen(rt)} ${prettyParen(
          cmd
        )} ${as.map((a, _) => prettyParen(a)).mkString(" ")}"

    case Wk(tm)     => pretty(tm)(ns.tail)
    case Irrelevant => "Ir"

    case Meta(id)         => s"?$id"
    case AppPruning(f, _) => s"?*${prettyParen(f)}"

  def pretty(d: Def): String = d match
    case DDef(m, x, t, SMeta, v) =>
      s"def $m/$x : ${pretty(t)(Nil)} = ${pretty(v)(Nil)}"
    case DDef(m, x, t, STy(_), v) =>
      s"def $m/$x : ${pretty(t)(Nil)} := ${pretty(v)(Nil)}"

  def pretty(ds: Defs): String = ds.toList.map(pretty).mkString("\n")
