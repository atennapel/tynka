package core

import common.Common.*
import common.Debug.*
import Evaluation.{eval as eval0, quote as quote0, apply, force}
import Pretty.pretty as pretty0
import Zonking.zonk as zonk0
import Syntax.*
import Value.*
import Metas.freshMeta

import scala.annotation.tailrec

type Types = Map[Name, (Lvl, VTy, VUniv)]

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

  def bind(x: Bind, ty: VTy, univ: VUniv, inserted: Boolean = false): Ctx =
    val newtypes = x match
      case DoBind(x) if !inserted => types + (x -> (lvl, ty, univ))
      case _                      => types
    Ctx(
      lvl + 1,
      VVar(lvl) :: env,
      Bound(locals, x, quote(ty), quote(univ)),
      Some(Expl) :: pruning,
      newtypes,
      pos
    )

  def define(
      x: Name,
      ty: VTy,
      qty: Ty,
      univ: VUniv,
      quniv: Univ,
      value: Val,
      qvalue: Tm
  ): Ctx =
    Ctx(
      lvl + 1,
      value :: env,
      Defined(locals, x, qty, quniv, qvalue),
      None :: pruning,
      types + (x -> (lvl, ty, univ)),
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
  def closeVTy(b: VTy): VTy = eval0(closeTy(quote(b)))(Nil)

  def lookup(x: Name): Option[(Ix, VTy, VUniv)] =
    types.get(x).map((k, ty, u) => (k.toIx(lvl), ty, u))

  def prettyLocals: String =
    def go(p: Locals): List[String] = p match
      case Empty              => Nil
      case Bound(p, x, ty, _) => s"$x : ${pretty0(zonk(ty))(p.names)}" :: go(p)
      case Defined(p, x, ty, _, v) =>
        s"$x : ${pretty0(zonk(ty))(p.names)} = ${pretty0(zonk(v))(p.names)}" :: go(
          p
        )
    go(locals).mkString("\n")

  def newMeta(ty: VTy, u: VUniv): Tm = force(ty) match
    case VUnitType() => Prim(PUnit)
    case _ =>
      val closed = closeVTy(ty)
      val m = freshMeta(closed, u)
      debug(s"newMeta ?$m : ${pretty(ty)}")
      AppPruning(Meta(m), pruning)

object Ctx:
  def empty(pos: PosInfo = (-1, -1)): Ctx =
    Ctx(lvl0, Nil, Empty, Nil, Map.empty, pos)

enum Locals:
  case Empty
  case Bound(locals: Locals, x: Bind, ty: Ty, univ: Univ)
  case Defined(locals: Locals, x: Name, ty: Ty, univ: Univ, tm: Tm)

  def closeTy(b: Ty): Ty = this match
    case Empty                   => b
    case Bound(ls, x, a, _)      => ls.closeTy(Pi(x, Expl, a, b))
    case Defined(ls, x, a, _, v) => ls.closeTy(Let(x, a, v, b))

  def names: List[Name] = this match
    case Empty                   => Nil
    case Bound(ls, x, _, _)      => x.toName :: ls.names
    case Defined(ls, x, _, _, _) => x :: ls.names
export Locals.*
