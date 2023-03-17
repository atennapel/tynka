package core

import common.Common.*
import Syntax.*
import Value.*
import Metas.*
import Globals.*

import scala.annotation.tailrec

object Evaluation:
  extension (c: Clos)
    def apply(v: Val): Val = c match
      case CClos(env, tm) => eval(tm)(v :: env)
      case CFun(fn)       => fn(v)

  extension (c: TConClos)
    def apply(v: Val): List[List[Val]] =
      c.cs.map(as => as.map(t => eval(t)(v :: c.env)))

  extension (c: Clos2)
    def apply(v: Val, w: Val): Val = c match
      case CClos2(env, tm) => eval(tm)(w :: v :: env)
      case CFun2(f)        => f(v, w)

  // evaluation
  private def vglobal(m: String, x: Name): Val =
    val value = getGlobal(m, x).get.value
    VGlobal(m, x, SId, () => value)

  def vapp(f: Val, a: Val, i: Icit): Val = f match
    case VLam(_, _, _, b) => b(a)
    case VRigid(hd, sp)   => VRigid(hd, SApp(sp, a, i))
    case VFlex(hd, sp)    => VFlex(hd, SApp(sp, a, i))
    case VGlobal(m, x, sp, v) =>
      VGlobal(m, x, SApp(sp, a, i), () => vapp(v(), a, i))
    case _ => impossible()

  def vappE(f: Val, a: Val): Val = vapp(f, a, Expl)
  def vappI(f: Val, a: Val): Val = vapp(f, a, Impl)

  def vquote(v: Val): Val = v match
    case VRigid(hd, SSplice(sp))        => VRigid(hd, sp)
    case VFlex(hd, SSplice(sp))         => VFlex(hd, sp)
    case VGlobal(m, hd, SSplice(sp), v) => VGlobal(m, hd, sp, () => vquote(v()))
    case v                              => VQuote(v)

  def vsplice(v: Val): Val = v match
    case VQuote(v)            => v
    case VRigid(hd, sp)       => VRigid(hd, SSplice(sp))
    case VFlex(hd, sp)        => VFlex(hd, SSplice(sp))
    case VGlobal(m, x, sp, v) => VGlobal(m, x, SSplice(sp), () => vsplice(v()))
    case _                    => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId            => v
    case SApp(sp, a, i) => vapp(vspine(v, sp), a, i)
    case SSplice(sp)    => vsplice(vspine(v, sp))

  private def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_, _)  => VMeta(id)

  def vappPruning(v: Val, p: Pruning)(implicit env: Env): Val =
    (env, p) match
      case (Nil, Nil)               => v
      case (a :: env, Some(i) :: p) => vapp(vappPruning(v, p)(env), a, i)
      case (_ :: env, None :: p)    => vappPruning(v, p)(env)
      case _                        => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Var(ix)               => env(ix.expose)
    case Global(m, x)          => vglobal(m, x)
    case Let(_, _, _, _, v, b) => eval(b)(eval(v) :: env)
    case U(s)                  => VU(s.map(eval))

    case TFun(a, vf, b)   => VTFun(eval(a), eval(vf), eval(b))
    case Pi(x, i, t, b)   => VPi(x, i, eval(t), Clos(b))
    case Lam(x, i, ty, b) => VLam(x, i, eval(ty), Clos(b))
    case App(f, a, i)     => vapp(eval(f), eval(a), i)
    case Fix(ty, rty, g, x, b, arg) =>
      VFix(eval(ty), eval(rty), g, x, CClos2(env, b), eval(arg))

    case VF    => VVF
    case VFVal => VVal
    case VFFun => VFun

    case Lift(vf, t) => VLift(eval(vf), eval(t))
    case Quote(t)    => vquote(eval(t))
    case Splice(t)   => vsplice(eval(t))

    case Wk(tm)     => eval(tm)(env.tail)
    case Irrelevant => VIrrelevant

    case Meta(id)         => vmeta(id)
    case AppPruning(t, p) => vappPruning(eval(t), p)

  // forcing
  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  // quotation
  @tailrec
  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VFlex(id, sp) =>
      getMeta(id) match
        case Solved(v, _, _) => force(vspine(v, sp), unfold)
        case Unsolved(_, _)  => v
    case VGlobal(_, _, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case _                                          => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SSplice(tm)      => quote(hd, tm, unfold).splice

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)

  def quoteS(s: VStage, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): CStage =
    s.map(v => quote(v, unfold))

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)       => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)        => quote(Meta(id), sp, unfold)
      case VGlobal(m, x, sp, _) => quote(Global(m, x), sp, unfold)
      case VU(s)                => U(quoteS(s))

      case VVF  => VF
      case VVal => VFVal
      case VFun => VFFun

      case VTFun(a, vf, b) =>
        TFun(quote(a, unfold), quote(vf, unfold), quote(b, unfold))
      case VLam(x, i, ty, b) =>
        Lam(x, i, quote(ty, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VFix(ty, rty, g, x, b, arg) =>
        Fix(
          quote(ty, unfold),
          quote(rty, unfold),
          g,
          x,
          quote(b(VVar(l), VVar(l + 1)), unfold)(l + 2),
          quote(arg, unfold)
        )

      case VLift(vf, t) => Lift(quote(vf, unfold), quote(t, unfold))
      case VQuote(t)    => quote(t, unfold).quote

      case VIrrelevant => Irrelevant

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)
