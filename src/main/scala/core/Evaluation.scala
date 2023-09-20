package core

import common.Common.*
import Syntax.*
import Value.*
import Metas.*

import scala.annotation.tailrec

object Evaluation:
  // closures
  extension (c: Clos[Tm1])
    inline def apply(v: Val1): Val1 = eval1(c.tm)(E1(c.env, v))

  extension (c: Clos[Tm0])
    inline def dive(implicit l: Lvl): Val0 = eval0(c.tm)(E0(c.env, l))

  // evaluation
  @tailrec
  def vvar0(ix: Ix)(implicit e: Env): Lvl = e match
    case E0(_, lvl) if ix.expose == 0 => lvl
    case E0(env, _)                   => vvar0(ix - 1)(env)
    case E1(env, _)                   => vvar0(ix - 1)(env)
    case EEmpty                       => impossible()

  @tailrec
  def vvar1(ix: Ix)(implicit e: Env): Val1 = e match
    case E1(_, v) if ix.expose == 0 => v
    case E0(env, _)                 => vvar1(ix - 1)(env)
    case E1(env, _)                 => vvar1(ix - 1)(env)
    case EEmpty                     => impossible()

  inline def vmeta(id: MetaId): Val1 = getMeta(id) match
    case Unsolved(_)      => VFlex(id, SId)
    case Solved(value, _) => VUnfold(id, SId, () => value)

  inline def vsplice(v: Val1): Val0 = v match
    case VQuote(v) => v
    case v         => VSplice(v)

  inline def vquote(v: Val0): Val1 = v match
    case VSplice(v) => v
    case v          => VQuote(v)

  def vapp1(f: Val1, a: Val1, i: Icit): Val1 = f match
    case VLam1(x, _, _, b) => b(a)
    case VFlex(id, sp)     => VFlex(id, SApp(sp, a, i))
    case VRigid(h, sp)     => VRigid(h, SApp(sp, a, i))
    case VUnfold(h, sp, v) => VUnfold(h, SApp(sp, a, i), () => vapp1(v(), a, i))
    case _                 => impossible()

  def vspine(v: Val1, sp: Spine): Val1 = sp match
    case SId            => v
    case SApp(sp, a, i) => vapp1(vspine(v, sp), a, i)

  def vappPruning(v: Val1, p: Pruning)(implicit env: Env): Val1 = (env, p) match
    case (EEmpty, Nil)                 => v
    case (E1(env, u), PESkip :: p)     => vappPruning(v, p)(env)
    case (E1(env, u), PEBind1(i) :: p) => vapp1(vappPruning(v, p)(env), u, i)
    case (E0(env, lvl), PEBind0 :: p) =>
      vapp1(vappPruning(v, p)(env), VQuote(VVar0(lvl)), Expl)
    case _ => impossible()

  def eval0(t: Tm0)(implicit env: Env): Val0 = t match
    case Var0(ix)          => VVar0(vvar0(ix))
    case Let0(x, ty, v, b) => VLet0(x, eval1(ty), eval0(v), Clos(b))
    case Lam0(x, ty, b)    => VLam0(x, eval1(ty), Clos(b))
    case App0(f, a)        => VApp0(eval0(f), eval0(a))
    case Splice(t)         => vsplice(eval1(t))
    case Wk10(t)           => eval0(t)(env.wk1)

  def eval1(t: Tm1)(implicit env: Env): Val1 = t match
    case Var1(ix)          => vvar1(ix)
    case Let1(_, _, v, b)  => eval1(b)(E1(env, eval1(v)))
    case U0(cv)            => VU0(eval1(cv))
    case U1                => VU1
    case Pi(x, i, ty, b)   => VPi(x, i, eval1(ty), Clos(b))
    case Lam1(x, i, ty, b) => VLam1(x, i, eval1(ty), Clos(b))
    case App1(f, a, i)     => vapp1(eval1(f), eval1(a), i)
    case Fun(p, cv, r)     => VFun(eval1(p), eval1(cv), eval1(r))
    case CV1               => VCV1
    case Comp              => VComp
    case Val               => VVal
    case Lift(cv, ty)      => VLift(eval1(cv), eval1(ty))
    case Quote(tm)         => vquote(eval0(tm))
    case AppPruning(tm, p) => vappPruning(eval1(tm), p)
    case Wk01(tm)          => eval1(tm)(env.wk0)
    case Wk11(tm)          => eval1(tm)(env.wk1)
    case Meta(id)          => vmeta(id)

  // forcing
  def force1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => VUnfold(id, SId, () => vspine(v, sp))
    case v => v

  @tailrec
  def forceAll1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => forceAll1(vspine(v, sp))
    case VUnfold(_, _, v) => forceAll1(v())
    case v                => v

  @tailrec
  def forceAll0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceAll1(v) match
        case VQuote(v) => forceAll0(v)
        case _         => top
    case v => v

  @tailrec
  def forceMetas1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => forceMetas1(vspine(v, sp))
    case VUnfold(_, _, v) => forceMetas1(v())
    // TODO: leave globals unforced
    case v => v

  @tailrec
  def forceMetas0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceMetas1(v) match
        case VQuote(v) => forceMetas0(v)
        case _         => top
    case v => v

  // quoting
  enum QuoteOption:
    case UnfoldAll
    case UnfoldMetas
    case UnfoldNone
    case LiftVars(lvl: Lvl)
  export QuoteOption.*

  private def quote1(h: Tm1, sp: Spine, q: QuoteOption)(implicit
      lvl: Lvl
  ): Tm1 = sp match
    case SId            => h
    case SApp(sp, v, i) => App1(quote1(h, sp, q), quote1(v, q), i)

  def quote1(v: Val1, q: QuoteOption)(implicit lvl: Lvl): Tm1 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goSp(h: Tm1, sp: Spine): Tm1 = quote1(h, sp, q)
    inline def goClos(c: Clos[Tm1]): Tm1 = quote1(c(VVar1(lvl)), q)(lvl + 1)
    inline def force(v: Val1): Val1 = q match
      case UnfoldAll   => forceAll1(v)
      case UnfoldMetas => forceMetas1(v)
      case UnfoldNone  => force1(v)
      case LiftVars(_) => force1(v)
    force(v) match
      case VRigid(lvl, sp)    => goSp(Var1(lvl.toIx), sp)
      case VFlex(id, sp)      => goSp(Meta(id), sp)
      case VUnfold(id, sp, _) => goSp(Meta(id), sp)
      case VPi(x, i, ty, b)   => Pi(x, i, go1(ty), goClos(b))
      case VLam1(x, i, ty, b) => Lam1(x, i, go1(ty), goClos(b))
      case VU0(cv)            => U0(go1(cv))
      case VU1                => U1
      case VFun(pty, cv, rty) => Fun(go1(pty), go1(cv), go1(rty))
      case VCV1               => CV1
      case VComp              => Comp
      case VVal               => Val
      case VLift(cv, ty)      => Lift(go1(cv), go1(ty))
      case VQuote(tm)         => Quote(go0(tm))

  def quote0(v: Val0, q: QuoteOption)(implicit lvl: Lvl): Tm0 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goClos(c: Clos[Tm0]): Tm0 = quote0(c.dive, q)(lvl + 1)
    inline def force(v: Val0): Val0 = q match
      case UnfoldAll   => forceAll0(v)
      case UnfoldMetas => forceMetas0(v)
      case UnfoldNone  => v
      case LiftVars(_) => v
    force(v) match
      case VVar0(x) =>
        q match
          case LiftVars(y) if x < y => Splice(Var1(x.toIx))
          case _                    => Var0(x.toIx)
      case VLet0(x, ty, v, b) => Let0(x, go1(ty), go0(v), goClos(b))
      case VLam0(x, ty, b)    => Lam0(x, go1(ty), goClos(b))
      case VApp0(f, a)        => App0(go0(f), go0(a))
      case VSplice(tm)        => Splice(go1(tm))
