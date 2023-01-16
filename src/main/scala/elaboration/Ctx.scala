package elaboration

import common.Common.*
import common.Debug.*
import core.Evaluation.{
  eval as eval0,
  quote as quote0,
  apply
}
import core.Pretty.pretty as pretty0
import core.Zonking.zonk as zonk0
import core.Syntax.*
import core.Value.*
import core.Locals
import core.Locals.*

import scala.annotation.tailrec

type Types = Map[Name, (Lvl, VTy, Stage)]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    locals: Locals,
    pruning: Pruning,
    types: Types,
    pos: PosInfo
):
  def names: List[Name] = locals.names

  def fresh(x: Name): Name = x.fresh(names)
  def fresh(x: Bind): Bind = x.fresh(names)

  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def bind(
      x: Bind,
      ty: VTy,
      stage: Stage,
      inserted: Boolean = false
  ): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => types + (x -> (lvl, ty, stage))
      case _                      => types
    Ctx(
      lvl + 1,
      VVar(lvl) :: env,
      Bound(locals, x, quote(ty), stage),
      Some(Expl) :: pruning,
      newtypes,
      pos
    )

  def define(
      x: Name,
      ty: VTy,
      qty: Ty,
      stage: Stage,
      value: Val,
      qvalue: Tm
  ): Ctx =
    Ctx(
      lvl + 1,
      value :: env,
      Defined(locals, x, qty, stage, qvalue),
      None :: pruning,
      types + (x -> (lvl, ty, stage)),
      pos
    )

  def eval(tm: Tm): Val = eval0(tm)(env)
  def quote(v: Val): Tm = quote0(v)(lvl)
  def zonk(t: Tm): Tm = zonk0(t)(lvl, env)
  def zonk(v: Val): Tm = zonk(quote(v))

  def close(v: Val): Clos = Clos(quote0(v)(lvl + 1))(env)
  def inst(c: Clos): Val = c(VVar(lvl))

  def pretty(tm: Tm): String = pretty0(zonk(tm))(names)
  def pretty(v: Val): String = pretty(quote(v))

  def closeTy(b: Ty): Ty = locals.closeTy(b)
  def closeVTy(b: VTy): VTy =
    val t = closeTy(quote(b))
    eval0(t)(Nil)

  def lookup(x: Name): Option[(Ix, VTy, Stage)] =
    types.get(x).map((k, ty, s) => (k.toIx(lvl), ty, s))

  def prettyLocals: String =
    def go(p: Locals): List[String] = p match
      case Empty              => Nil
      case Bound(p, x, ty, _) => s"$x : ${pretty0(zonk(ty))(p.names)}" :: go(p)
      case Defined(p, x, ty, _, v) =>
        s"$x : ${pretty0(zonk(ty))(p.names)} = ${pretty0(zonk(v))(p.names)}" :: go(
          p
        )
    go(locals).mkString("\n")

object Ctx:
  def empty(pos: PosInfo = (-1, -1)): Ctx =
    Ctx(lvl0, Nil, Empty, Nil, Map.empty, pos)
