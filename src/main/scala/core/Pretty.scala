package core

import common.Common.*
import Syntax.*

import scala.annotation.tailrec

object Pretty:
  private def prettyApp(tm: Tm)(implicit ns: List[Name]): String = tm match
    case App(f, a, Expl) => s"${prettyApp(f)} ${prettyParen(a)}"
    case App(f, a, Impl) => s"${prettyApp(f)} {${pretty(a)}}"
    case f               => prettyParen(f)

  private def prettyPi(tm: Tm)(implicit ns: List[Name]): String = tm match
    case TFun(a, _, b) => s"${prettyParen(a, true)} -> ${prettyPi(b)}"
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
      case Meta(_)             => pretty(tm)
      case Lift(_, _)          => pretty(tm)
      case Quote(_)            => pretty(tm)
      case Splice(_)           => pretty(tm)
      case AppPruning(_, _)    => pretty(tm)
      case App(_, _, _) if app => pretty(tm)
      case U(_)                => pretty(tm)
      case Irrelevant          => pretty(tm)
      case Wk(tm)              => prettyParen(tm, app)(ns.tail)
      case VF                  => pretty(tm)
      case VFVal               => pretty(tm)
      case VFFun               => pretty(tm)
      case TInt                => pretty(tm)
      case IntLit(_)           => pretty(tm)
      case _                   => s"(${pretty(tm)})"

  private def prettyLift(x: Name, tm: Tm)(implicit ns: List[Name]): String =
    pretty(tm)(x :: ns)

  def pretty(s: CStage)(implicit ns: List[Name]): String = s"${s.map(pretty)}"

  def pretty(tm: Tm)(implicit ns: List[Name]): String = tm match
    case Var(ix)      => s"${ns(ix.expose)}"
    case Global(m, x) => s"$m:$x"
    case Let(x0, t, s, _, v, b) =>
      val x = x0.fresh
      val ss = s match
        case SMeta  => ""
        case STy(_) => ":"
      s"let $x : ${pretty(t)} $ss= ${pretty(v)}; ${prettyLift(x, b)}"
    case U(s) => pretty(s)

    case VF    => "VF"
    case VFVal => "Val"
    case VFFun => "Fun"

    case Pi(_, _, _, _)  => prettyPi(tm)
    case TFun(_, _, _)   => prettyPi(tm)
    case Lam(_, _, _, _) => prettyLam(tm)
    case App(_, _, _)    => prettyApp(tm)

    case Fix(_, _, g0, x0, b, arg) =>
      val g = g0.fresh
      val x = x0.fresh
      s"fix ($g $x. ${prettyParen(b)(x.toName :: g.toName :: ns)}) ${prettyParen(arg)}"

    case Lift(_, t) => s"^${prettyParen(t)}"
    case Quote(t)   => s"`${prettyParen(t)}"
    case Splice(t)  => s"$$${prettyParen(t)}"

    case TInt      => "Int"
    case IntLit(n) => s"$n"

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
