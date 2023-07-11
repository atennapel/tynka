package jvmir

import common.Common.impossible
import Syntax.*

import scala.collection.mutable

object Interpreter:
  private type Ds = Map[GName, DDef]

  def interpret(d: Defs): Option[Tm] =
    implicit val fd: Ds = d.defs
      .flatMap(d =>
        d match
          case d @ DDef(x, _, _, _) => Some((x, d))
          case _                    => None
      )
      .toMap
    fd.get("main").map { d =>
      d.ty match
        case TDef(Some(l), _) if l.nonEmpty => impossible()
        case _                              =>
      implicit val stack: Stack = mutable.ArrayBuffer.empty
      implicit val frame: Frame = Frame(0)
      stack += frame
      interpret(d.value)
    }

  private def interpret(
      t: Tm
  )(implicit defs: Ds, frame: Frame, stack: Stack): Tm =
    t match
      case Arg(ix) => frame.args(ix)
      case Var(ix) => frame.vars(ix)

      case Global(x, _) =>
        implicit val newframe: Frame = Frame(0)
        stack += newframe
        val res = interpret(defs(x).value)
        stack.remove(stack.size - 1)
        res
      case GlobalApp(x, _, false, as) =>
        val newframe: Frame = Frame(as.map(interpret))
        stack += newframe
        val res = interpret(defs(x).value)(defs, newframe, stack)
        stack.remove(stack.size - 1)
        res
      case GlobalApp(x, _, true, as) =>
        val ias = as.map(interpret)
        ias.zipWithIndex.foreach((v, i) => frame.args(i) = v)
        frame.vars.clear()
        interpret(defs(x).value)

      case Let(ix, _, v, b) =>
        frame.vars(ix) = interpret(v)
        interpret(b)

      case IntLit(_)       => t
      case Con(dx, cx, as) => Con(dx, cx, as.map(interpret))

      case Field(_, _, scrut, ix) =>
        interpret(scrut) match
          case Con(_, _, as) => as(ix)
          case _             => impossible()

      case Match(_, _, ix, scrut, cs, other) =>
        interpret(scrut) match
          case v @ Con(_, dx, as) =>
            frame.vars(ix) = v
            cs.find((dx1, _) => dx1 == dx)
              .map(_._2)
              .orElse(other)
              .map(interpret)
              .getOrElse(impossible())
          case s => impossible()

  private type Stack = mutable.ArrayBuffer[Frame]

  private case class Frame(args: Array[Tm], vars: mutable.Map[LName, Tm])

  private object Frame:
    def apply(argsCount: Int): Frame =
      Frame(Array.ofDim(argsCount), mutable.Map.empty)

    def apply(args: List[Tm]): Frame =
      Frame(Array.from(args), mutable.Map.empty)
