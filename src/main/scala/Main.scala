import surface.Parser.defsParser
import common.Debug.*
import core.Pretty.pretty
import core.Staging.stage
import elaboration.Elaboration.ElaborateError
import elaboration.ModuleLoading.load
import ir.JvmGenerator.generate

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename0: String): Unit =
    setDebug(false)
    try
      val etimeStart = System.nanoTime()
      val (filename, eds) = load(filename0)
      val moduleName = filename.split("/").last
      val etime = System.nanoTime() - etimeStart
      println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")

      println(pretty(eds))

      println("\nstaging:")
      val irds = stage(filename, eds)
      println(irds)

      println("\ngenerate JVM bytecode")
      generate(filename, irds)
    catch
      case err: ElaborateError =>
        println(err.getMessage)
        val (line, col) = err.pos
        if line > 0 && col > 0 then
          val stream = Source.fromURL(err.uri)
          val lineSrc = stream.getLines.toSeq(line - 1)
          stream.close()
          println(lineSrc)
          println(s"${" " * (col - 1)}^")
          println(s"in ${err.uri}")
        if isDebug then err.printStackTrace()
