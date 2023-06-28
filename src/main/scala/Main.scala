import surface.Parser.defsParser

import java.io.File
import scala.io.Source
import parsley.io.given

object Main:
  @main def run(filename: String): Unit =
    val text = Source.fromFile(filename).mkString
    val defs = defsParser
      .parse(text)
      .toTry
      .get
    println(defs)
