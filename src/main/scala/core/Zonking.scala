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

  private def proj(t: VT, p: ProjType, ty: Tm, pty: Tm): VT =
    t.fold(v => Left(vproj(v, p)), t => Right(Proj(t, p, ty, pty)))

  private def splice(t: VT): VT =
    t.fold(v => Left(vsplice(v)), t => Right(t.splice))

  private def meta(id: MetaId)(implicit l: Lvl, e: Env): VT =
    getMeta(id) match
      case Solved(_, v, _, _)   => Left(v)
      case Unsolved(_, _, _, _) => Right(Meta(id))

  private def zonkSp(t: Tm)(implicit l: Lvl, e: Env): VT = t match
    case Meta(id)            => meta(id)
    case AppPruning(t, p)    => Left(vappPruning(eval(t), p))
    case App(f, a, i)        => app(zonkSp(f), a, i)
    case Proj(t, p, ty, pty) => proj(zonkSp(t), p, ty, pty)
    case Splice(t)           => splice(zonkSp(t))
    case Wk(t)               => zonkSp(t)(l - 1, e.tail).map(Wk(_))
    case t                   => Right(zonk(t))

  def zonk(t: Tm)(implicit l: Lvl, e: Env): Tm = t match
    case Var(ix)      => t
    case Global(_, _) => t
    case Prim(x)      => t
    case Irrelevant   => t
    case IntLit(_)    => t
    case StringLit(_) => t
    case Let(u, x, t, s, bt, v, b) =>
      Let(u, x, zonk(t), s, zonk(bt), zonk(v), zonkLift(b))
    case U(s) => U(s.map(zonk))

    case Pi(u, x, i, t, b) => Pi(u, x, i, zonk(t), zonkLift(b))
    case Fun(u, a, b, c)   => Fun(u, zonk(a), zonk(b), zonk(c))
    case Lam(x, i, ty, b)  => Lam(x, i, zonk(ty), zonkLift(b))
    case App(_, _, _)      => quoteVT(zonkSp(t))
    case Fix(ty, rty, g, x, b, arg) =>
      Fix(
        zonk(ty),
        zonk(rty),
        g,
        x,
        zonk(b)(l + 2, VVar(l + 1) :: VVar(l) :: e),
        zonk(arg)
      )

    case Sigma(x, t, b) => Sigma(x, zonk(t), zonkLift(b))
    case Pair(a, b, t)  => Pair(zonk(a), zonk(b), zonk(t))
    case Proj(_, _, _, _) =>
      quoteVT(zonkSp(t)) match
        case Proj(t, p, ty, pty) => Proj(t, p, zonk(ty), zonk(pty))
        case t                   => t

    case Lift(cv, t) => Lift(zonk(cv), zonk(t))
    case Quote(t)    => zonk(t).quote
    case Splice(_)   => quoteVT(zonkSp(t))

    case Foreign(io, rt, cmd, as) =>
      Foreign(io, zonk(rt), zonk(cmd), as.map((a, t) => (zonk(a), zonk(t))))

    case Data(x, cs) =>
      Data(x, cs.map((c, as) => (c, as.map((x, a) => (x, zonkLift(a))))))
    case Con(x, t, as) => Con(x, zonk(t), as.map(zonk))
    case Match(dty, rty, scrut, cs, other) =>
      Match(
        zonk(dty),
        zonk(rty),
        zonk(scrut),
        cs.map((x, c, i, b) => (x, c, i, zonk(b))),
        other.map(zonk)
      )

    case Wk(tm) => Wk(zonk(tm)(l - 1, e.tail))

    case Meta(id)         => quoteVT(meta(id))
    case AppPruning(_, _) => quoteVT(zonkSp(t))
