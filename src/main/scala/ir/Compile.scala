package ir

import common.Common.*
import common.Ref
import core.Globals.*
import core.Evaluation.stage
import Monomorphize.{monomorphize, monomorphizedDatatypes}
import Simplify.simplify

// TODO: compile to JVM IR
object Compile:
  def compile(): Unit =
    val defs = allGlobals.flatMap {
      case GlobalEntry0(x, tm, ty, cv, vv, vty, vcv) =>
        val mty = monomorphize(ty)
        implicit val ref = Ref(0)
        val mtm = monomorphize(stage(tm))
        simplify(x, mtm, mty)
      case _ => Nil
    }

    monomorphizedDatatypes.foreach { (x, cs) =>
      cs match
        case Nil => println(s"data $x")
        case cs =>
          val scs = cs
            .map { (c, as) =>
              as match
                case Nil => s"$c"
                case as =>
                  val sas = as
                    .map {
                      case (DontBind, t)  => s"$t"
                      case (DoBind(x), t) => s"($x : $t)"
                    }
                    .mkString(" ")
                  s"$c $sas"
            }
            .mkString(" | ")
          println(s"data $x := $scs")
    }

    defs.foreach((x, ty, v) => println(s"def $x : $ty := $v"))
