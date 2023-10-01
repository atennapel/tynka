package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.{
  QuoteOption,
  UnfoldNone,
  UnfoldMetas,
  quote1 as quote1_,
  eval1 as eval1_,
  quote0 as quote0_,
  eval0 as eval0_
}
import Pretty.{pretty0 as pretty0_, pretty1 as pretty1_}

import scala.annotation.tailrec

enum NameInfo:
  case Name0(_lvl: Lvl, ty: VTy, cv: VCV)
  case Name1(_lvl: Lvl, ty: VTy)
  def lvl: Lvl = this match
    case Name0(_lvl, ty, cv) => _lvl
    case Name1(_lvl, ty)     => _lvl
export NameInfo.*
private type NameMap = Map[Name, NameInfo]

final case class Ctx(
    lvl: Lvl,
    env: Env,
    locals: Locals,
    pruning: Pruning,
    binds: List[Bind],
    names: NameMap,
    pos: PosInfo
):
  private def addName(x: Bind, info: NameInfo): NameMap =
    x match
      case DontBind  => names
      case DoBind(x) => names + (x -> info)

  def typeOfLvl(x: Lvl): Ty =
    def go(ls: Locals, i: Int): Ty = ls match
      case LEmpty                        => impossible()
      case LDef(locs, ty, _) if i == 0   => ty
      case LBind0(locs, ty, _) if i == 0 => ty
      case LBind1(locs, ty) if i == 0    => ty
      case LDef(ls, _, _)                => go(ls, i - 1)
      case LBind0(ls, _, _)              => go(ls, i - 1)
      case LBind1(ls, _)                 => go(ls, i - 1)
    go(locals, x.toIx(lvl).expose)

  def bindOfLvl(x: Lvl): Bind = binds.reverse(x.expose)

  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def lookup(x: Name): Option[NameInfo] = names.get(x)

  def bind1(x: Bind, ty: Ty, vty: VTy): Ctx =
    Ctx(
      lvl + 1,
      E1(env, VVar1(lvl)),
      LBind1(locals, ty),
      PEBind1(Expl) :: pruning,
      x :: binds,
      addName(x, Name1(lvl, vty)),
      pos
    )

  def insert1(x: Bind, ty: Ty): Ctx =
    Ctx(
      lvl + 1,
      E1(env, VVar1(lvl)),
      LBind1(locals, ty),
      PEBind1(Expl) :: pruning,
      x :: binds,
      names,
      pos
    )

  def define(x: Name, ty: Ty, vty: VTy, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      E1(env, vv),
      LDef(locals, ty, v),
      PESkip :: pruning,
      DoBind(x) :: binds,
      names + (x -> Name1(lvl, vty)),
      pos
    )

  def defineInsert(x: Name, ty: Ty, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      E1(env, vv),
      LDef(locals, ty, v),
      PESkip :: pruning,
      DoBind(x) :: binds,
      names,
      pos
    )

  def bind0(x: Bind, ty: Ty, vty: VTy, cv: CV, vcv: VCV): Ctx =
    Ctx(
      lvl + 1,
      E0(env, VVar0(lvl)),
      LBind0(locals, ty, cv),
      PEBind0 :: pruning,
      x :: binds,
      addName(x, Name0(lvl, vty, vcv)),
      pos
    )

  def insert0(x: Bind, ty: Ty, cv: CV): Ctx =
    Ctx(
      lvl + 1,
      E0(env, VVar0(lvl)),
      LBind0(locals, ty, cv),
      PEBind0 :: pruning,
      x :: binds,
      names,
      pos
    )

  def quote1(v: Val1, q: QuoteOption = UnfoldNone): Tm1 = quote1_(v, q)(lvl)
  def quote0(v: Val0, q: QuoteOption = UnfoldNone): Tm0 = quote0_(v, q)(lvl)
  def eval1(t: Tm1): Val1 = eval1_(t)(env)
  def eval0(t: Tm0): Val0 = eval0_(t)(env)

  def pretty1(v: Val1, q: QuoteOption = UnfoldMetas): String =
    pretty1_(quote1_(v, q)(lvl))(binds)
  def pretty0(v: Val0, q: QuoteOption = UnfoldMetas): String =
    pretty0_(quote0_(v, q)(lvl))(binds)
  def pretty1(v: Tm1): String =
    pretty1_(v)(binds)
  def pretty0(v: Tm0): String =
    pretty0_(v)(binds)

object Ctx:
  def empty(pos: PosInfo) = Ctx(lvl0, EEmpty, LEmpty, Nil, Nil, Map.empty, pos)
