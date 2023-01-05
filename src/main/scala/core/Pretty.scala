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
        case Lam(x0, Expl, b) =>
          val x = x0.fresh
          s"${if first then "" else " "}$x${go(b)(x.toName :: ns)}"
        case Lam(x0, Impl, b) =>
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
      case Global(_)           => pretty(tm)
      case Prim(_)             => pretty(tm)
      case Pair(_, _)          => pretty(tm)
      case Proj(_, _)          => pretty(tm)
      case Meta(_)             => pretty(tm)
      case Lift(_, _)          => pretty(tm)
      case Quote(_)            => pretty(tm)
      case Splice(_)           => pretty(tm)
      case AppPruning(_, _)    => pretty(tm)
      case App(_, _, _) if app => pretty(tm)
      case Wk(tm)              => prettyParen(tm, app)(ns.tail)
      case _                   => s"(${pretty(tm)})"

  private def flattenPair(tm: Tm): List[Tm] = tm match
    case Pair(fst, snd) => fst :: flattenPair(snd)
    case tm             => List(tm)

  private def prettyLift(x: Name, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x :: ns)

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Var(ix)   => s"${ns(ix.expose)}"
    case Global(x) => s"$x"
    case Prim(x)   => s"$x"
    case Let(x0, t, v, b) =>
      val x = x0.fresh
      s"let $x : ${pretty(t)} = ${pretty(v)}; ${prettyLift(x, b)}"

    case Pi(_, _, _, _) => prettyPi(tm)
    case Lam(_, _, _)   => prettyLam(tm)
    case App(_, _, _)   => prettyApp(tm)

    case Sigma(_, _, _) => prettySigma(tm)
    case Pair(_, _) =>
      val es = flattenPair(tm)
      if es.last == Prim(PUnit) then s"[${es.init.map(pretty).mkString(", ")}]"
      else s"(${es.map(pretty).mkString(", ")})"
    case Proj(t, p) => s"${prettyParen(t)}$p"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case Wk(tm) => pretty(tm)(ns.tail)

    case Meta(id)         => s"?$id"
    case AppPruning(f, _) => s"?*${prettyParen(f)}"

  def pretty(d: Def): String = d match
    case DDef(x, t, v) => s"def $x : ${pretty(t)(Nil)} = ${pretty(v)(Nil)}"

  def pretty(ds: Defs): String = ds.toList.map(pretty).mkString("\n")
