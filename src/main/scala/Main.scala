import surface.Parser.defsParser
import common.Debug.*

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename0: String): Unit =
    setDebug(false)
    var filename = filename0
    if !filename.endsWith(".tynka") then filename = s"$filename0.tynka"
    val moduleName = filename.dropRight(6).split("/").last
    // try
    val ptimeStart = System.nanoTime()
    val ds = defsParser.parseFromFile(new File(filename)).flatMap(_.toTry).get
    val ptime = System.nanoTime() - ptimeStart
    println(s"parser time: ${ptime / 1000000}ms (${ptime}ns)")
    println(ds)
    /*catch
      case err: ElaborateError =>
        println(err.getMessage)
        val (line, col) = err.pos
        if line > 0 && col > 0 then
          val stream = Source.fromFile(filename)
          val lineSrc = stream.getLines.toSeq(line - 1)
          stream.close()
          println(lineSrc)
          println(s"${" " * (col - 1)}^")
        if isDebug then err.printStackTrace()
     */
