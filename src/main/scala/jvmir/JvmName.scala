package jvmir

import scala.collection.mutable

object JvmName:
  // naming
  private val nameCache: mutable.Map[String, String] = mutable.Map.empty
  private val chars: Map[String, String] = Map(
    "`" -> "GRAVE",
    "~" -> "TILDE",
    "!" -> "EXCL",
    "@" -> "AT",
    "#" -> "HASH",
    // "$" -> "DOLLAR",
    "%" -> "PERCENT",
    "^" -> "HAT",
    "&" -> "AMPER",
    "*" -> "STAR",
    "-" -> "DASH",
    "+" -> "PLUS",
    "=" -> "EQUALS",
    "|" -> "PIPE",
    "\\" -> "BACK",
    ":" -> "COLON",
    ";" -> "SEMI",
    "," -> "COMMA",
    "<" -> "LT",
    "." -> "PERIOD",
    ">" -> "GT",
    "?" -> "QUESTION",
    "/" -> "SLASH"
  )

  def escape(x: String): String =
    nameCache.get(x) match
      case Some(y) => y
      case None =>
        if x == "main" then
          val y = "main$"
          nameCache += (x -> y)
          y
        else
          val y = x
            .split("")
            .map(x => chars.get(x).fold(x)(y => s"_${y}"))
            .mkString("")
          nameCache += (x -> y)
          y
