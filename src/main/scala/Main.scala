import surface.Parser.defsParser
import common.Common.Name
import common.Debug.*
import core.Pretty.pretty
import core.Globals.getGlobal
import core.Evaluation.nf
import elaboration.ModuleLoading.load
import elaboration.Elaboration.elaborate
import elaboration.Elaboration.ElaborateError
import core.Staging.stage
import ir.Compilation.compile
import jvmir.Interpreter.interpret
import jvmir.JvmGenerator.generate

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename0: String, options: String*): Unit =
    setDebug(false)
    try
      val etimeStart = System.nanoTime()
      val (filename, eds) = load(filename0)
      val etime = System.nanoTime() - etimeStart
      println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")
      println(pretty(eds))

      if options.contains("typecheck") then return

      /*
      getGlobal(Name("main")).foreach { g =>
        println("\nmain normal form:")
        println(pretty(nf(g.tm))(Nil))
      }*/

      println("\nstaging:")
      val irds = stage(eds)
      println(irds)

      if options.contains("stage") then return

      println("\ncompilation:")
      val jvmirds = compile(irds)
      println(jvmirds)

      if options.contains("compile") then return

      /*
      println("\ninterpret:")
      val interpretTimeStart = System.nanoTime()
      interpret(jvmirds).foreach(println(_))
      val interpretTime = System.nanoTime() - interpretTimeStart
      println(
        s"interpret time: ${interpretTime / 1000000}ms (${interpretTime}ns)"
      )
       */

      println("\ngenerate JVM bytecode")
      generate(filename, jvmirds)
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
