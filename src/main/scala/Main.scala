import surface.Parser.defsParser
import common.Common.*
import common.Debug.*
import common.Ref
import core.Syntax.*
import core.Value.*
import core.Primitives.*
import core.Evaluation.*
import core.Metas.*
import core.Ctx
import core.Globals.*
import core.Pretty.*
import core.Elaboration.{elaborate, ElaborateError}
import ir.Compile.compile
import jvmir.Generator.generate

import java.io.File
import scala.io.Source
import parsley.io.given
import scala.util.Using

object Main:
  @main def run(filename: String): Unit =
    setDebug(false)
    try
      implicit val ctx: Ctx = Ctx.empty((0, 0))

      val etimeStart = System.nanoTime()
      val text = Using(Source.fromFile(filename)) { source =>
        source.mkString
      }.get
      val sdefs = defsParser.parse(text).toTry.get
      elaborate(sdefs)
      val etime = System.nanoTime() - etimeStart
      println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")

      println()

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

      allGlobals.foreach {
        case GlobalEntry0(x, tm, ty, cv, vv, vty, vcv) =>
          println(s"def $x : ${ctx.pretty1(vty)} := ${ctx.pretty0(stage(tm))}")
        case GlobalEntry1(x, tm, ty, vv, vty) =>
          // println(tm)
          println(
            s"def $x : ${ctx.pretty1(vty)} = ${ctx.pretty1(tm)}"
          )
        case GlobalData0(x, newtype, Nil, lev, _) =>
          val begin = if newtype then "newtype" else "data"
          println(s"$begin $x : ${ctx.pretty1(U0(Val(lev)))}")
        case GlobalData0(x, newtype, ps, lev, _) =>
          val begin = if newtype then "newtype" else "data"
          val sps = ps
            .foldLeft((List.empty[String], List.empty[Bind])) {
              case ((res, binds), (i, x, t)) =>
                (i.wrap(s"$x : ${pretty1(t)(binds)}") :: res, x :: binds)
            }
            ._1
            .reverse
          println(
            s"$begin $x ${sps.mkString(" ")} : ${ctx.pretty1(U0(Val(lev)))}"
          )
        case GlobalCon0(x, dx, Nil) => println(s"| $x")
        case GlobalCon0(x, dx, ps) =>
          val binds = getGlobalData0(dx).params.map(_._2).reverse
          def showParam(x: Bind, lev: Tm1, t: Tm1) = x match
            case DontBind  => prettyParen1(t)(binds)
            case DoBind(x) => s"($x : ${pretty1(t)(binds)})"
          println(
            s"| $x ${ps.map(showParam).mkString(" ")}"
          )
      }

      println()

      val all = compile(Name("main"))
      all.foreach(println)

      val module = filename.dropRight(6)
      generate(module, all)
      println(s"generated $module.class")
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
          println(s"in ${filename}:$line:$col")
        if isDebug then err.printStackTrace()
