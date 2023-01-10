package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.*
import Metas.*

object Zonking:
  private type VT = Either[Val, Tm]

  private def quoteVT(t: VT)(implicit l: Lvl): Tm =
    t.fold(quote(_, UnfoldMetas), t => t)

  private def zonkLift(t: Tm)(implicit l: Lvl, e: Env): Tm =
    zonk(t)(l + 1, VVar(l) :: e)

  private def app(f: VT, a: Val, i: Icit)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, a, i)), t => Right(App(t, quote(a), i)))

  private def app(f: VT, a: Tm, i: Icit)(implicit l: Lvl, e: Env): VT =
    f.fold(v => Left(vapp(v, eval(a), i)), t => Right(App(t, zonk(a), i)))

  private def proj(t: VT, p: ProjType): VT =
    t.fold(v => Left(vproj(v, p)), t => Right(Proj(t, p)))

  private def splice(t: VT): VT =
    t.fold(v => Left(vsplice(v)), t => Right(Splice(t)))

  private def meta(id: MetaId)(implicit l: Lvl, e: Env): VT =
    getMeta(id) match
      case Solved(v, _, _) => Left(v)
      case Unsolved(_, _)  => Right(Meta(id))

  private def zonkSp(t: Tm)(implicit l: Lvl, e: Env): VT = t match
    case Meta(id)         => meta(id)
    case AppPruning(t, p) => Left(vappPruning(eval(t), p))
    case App(f, a, i)     => app(zonkSp(f), a, i)
    case Proj(t, p)       => proj(zonkSp(t), p)
    case Splice(t)        => splice(zonkSp(t))
    case Wk(t)            => zonkSp(t)(l - 1, e.tail).map(Wk(_))
    case t                => Right(t)

  def zonk(s: Stage[Ty])(implicit l: Lvl, e: Env): Stage[Ty] = s.map(zonk)

  def zonk(t: Tm)(implicit l: Lvl, e: Env): Tm = t match
    case Var(ix)            => t
    case Global(x)          => t
    case Prim(x)            => t
    case IntLit(n)          => t
    case Let(x, t, s, v, b) => Let(x, zonk(t), zonk(s), zonk(v), zonkLift(b))
    case U(s)               => U(zonk(s))

    case Pi(x, i, t, b)  => Pi(x, i, zonk(t), zonkLift(b))
    case FunTy(t, vf, b) => FunTy(zonk(t), zonk(vf), zonk(b))
    case Lam(x, i, b)    => Lam(x, i, zonkLift(b))
    case App(_, _, _)    => quoteVT(zonkSp(t))

    case Sigma(x, t, b) => Sigma(x, zonk(t), zonkLift(b))
    case PairTy(t, b)   => PairTy(zonk(t), zonk(b))
    case Pair(a, b)     => Pair(zonk(a), zonk(b))
    case Proj(_, _)     => quoteVT(zonkSp(t))

    case Lift(vf, t) => Lift(zonk(vf), zonk(t))
    case Quote(t)    => Quote(zonk(t))
    case Splice(_)   => quoteVT(zonkSp(t))

    case Wk(tm) => Wk(zonk(tm)(l - 1, e.tail))

    case Meta(id)         => quoteVT(meta(id))
    case AppPruning(_, _) => quoteVT(zonkSp(t))
