import surface.Parser.defsParser
import common.Debug.*

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename: String): Unit =
    setDebug(false)
    val ptimeStart = System.nanoTime()
    val tm = defsParser.parseFromFile(new File(filename)).flatMap(_.toTry).get
    val ptime = System.nanoTime() - ptimeStart
    println(s"parser time: ${ptime / 1000000}ms (${ptime}ns)")
    println(tm)
