import surface.Parser.defsParser
import common.Common.*
import common.Debug.*
import core.Elaboration.{elaborate, ElaborateError}
import core.Value.*
import core.Evaluation.*
import core.Metas.*
import core.Ctx
import core.Globals.*

import java.io.File
import scala.io.Source
import parsley.io.given
import core.Metas.getAllPostponed
import core.Metas.PostponedEntry

object Main:
  @main def run(filename: String): Unit =
    setDebug(false)
    try
      implicit val ctx: Ctx = Ctx.empty((0, 0))

      val etimeStart = System.nanoTime()
      val text = Source.fromFile(filename).mkString
      val sdefs = defsParser.parse(text).toTry.get
      elaborate(sdefs)
      val etime = System.nanoTime() - etimeStart
      println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")

      println()

      /*
      getMetas().foreach((m, t, v) =>
        v match
          case None => println(s"?$m : ${ctx.pretty1(t)}")
          case Some(v) =>
            println(s"?$m : ${ctx.pretty1(t)} = ${ctx.pretty1(v)}")
      )

      println()

      getAllPostponed().foreach((id, e) =>
        e match
          case PECheck1(ctx, tm, ty, m) =>
            println(s"?p$id as ?$m: $tm : ${ctx.pretty1(ty)}")
          case PECheckVarU1(ctx, x, ty, m) =>
            println(s"?p$id as ?$m: $x : ${ctx.pretty1(ty)}")
          case PECheck1Done(ctx, Some(tm)) =>
            println(s"?p$id = ${ctx.pretty1(tm)}")
          case PECheck1Done(ctx, None) => println(s"?p$id = ...")
      )

      println()
       */

      allGlobals.foreach {
        case GlobalEntry0(x, tm, ty, cv, vv, vty, vcv) =>
          println(s"$x : ${ctx.pretty1(vty)} := ${ctx.pretty0(stage(tm))}")
        case GlobalEntry1(x, tm, ty, vv, vty) =>
          println(
            s"$x : ${ctx.pretty1(vty)} = ${ctx.pretty1(tm)}"
          )
      }
    catch
      case err: ElaborateError =>
        println(err.getMessage)
        val (line, col) = err.pos
        if line > 0 && col > 0 then
          val stream = Source.fromFile(filename)
          val lineSrc = stream.getLines.toSeq(line - 1)
          stream.close()
          println(lineSrc)
          println(s"${" " * (col - 1)}^")
          println(s"in ${filename}")
        if isDebug then err.printStackTrace()
