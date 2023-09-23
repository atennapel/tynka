import surface.Parser.parser
import common.Common.*
import common.Debug.*
import core.Elaboration.{elaborate0, ElaborateError}
import core.Value.*
import core.Evaluation.*

import java.io.File
import scala.io.Source
import parsley.io.given
import core.Metas.getMetas
import core.Ctx

object Main:
  @main def run(filename: String): Unit =
    setDebug(false)
    try
      implicit val ctx: Ctx = Ctx.empty((0, 0))

      val etimeStart = System.nanoTime()
      val text = Source.fromFile(filename).mkString
      val stm = parser.parse(text).toTry.get
      val (tm, ty) = elaborate0(stm)
      val etime = System.nanoTime() - etimeStart
      println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")

      getMetas().foreach((m, t, v) =>
        v match
          case None    => println(s"?$m : ${ctx.pretty(t)}")
          case Some(v) => println(s"?$m : ${ctx.pretty(t)} = ${ctx.pretty(v)}")
      )

      println(tm)
      println(ty)
      println(stage(tm))
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
