package core

import common.Common.*
import Syntax.*
import Value.*

import scala.annotation.tailrec

final case class Ctx(lvl: Lvl, locals: Locals, binds: List[Bind]):
  def bind1(x: Bind, ty: Ty, vty: VTy): Ctx =
    Ctx(lvl + 1, LBind1(locals, ty), x :: binds)

object Ctx:
  val empty = Ctx(lvl0, LEmpty, Nil)
