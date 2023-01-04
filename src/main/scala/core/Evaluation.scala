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

  // evaluation
  private def vglobal(x: Name): Val =
    val value = getGlobal(x).get.value
    VGlobal(x, SId, () => value)

  def vapp(f: Val, a: Val, i: Icit): Val = f match
    case VLam(_, _, b)  => b(a)
    case VRigid(hd, sp) => VRigid(hd, SApp(sp, a, i))
    case VFlex(hd, sp)  => VFlex(hd, SApp(sp, a, i))
    case VGlobal(uri, sp, v) =>
      VGlobal(uri, SApp(sp, a, i), () => vapp(v(), a, i))
    case _ => impossible()

  def vproj(v: Val, p: ProjType): Val = v match
    case VPair(fst, snd) =>
      p match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VRigid(hd, sp)      => VRigid(hd, SProj(sp, p))
    case VFlex(hd, sp)       => VFlex(hd, SProj(sp, p))
    case VGlobal(uri, sp, v) => VGlobal(uri, SProj(sp, p), () => vproj(v(), p))
    case _                   => impossible()

  def vfst(v: Val): Val = vproj(v, Fst)
  def vsnd(v: Val): Val = vproj(v, Snd)

  private def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _) => v
    case Unsolved(_)  => VMeta(id)

  private def vspine(v: Val, sp: Spine): Val = sp match
    case SId             => v
    case SApp(sp, a, i)  => vapp(vspine(v, sp), a, i)
    case SProj(sp, proj) => vproj(vspine(v, sp), proj)

  def vappPruning(v: Val, p: Pruning)(implicit env: Env): Val =
    (env, p) match
      case (Nil, Nil)               => v
      case (a :: env, Some(i) :: p) => vapp(vappPruning(v, p)(env), a, i)
      case (_ :: env, None :: p)    => vappPruning(v, p)(env)
      case _                        => impossible()

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Var(ix)         => env(ix.expose)
    case Global(x)       => vglobal(x)
    case Let(_, _, v, b) => eval(b)(eval(v) :: env)
    case Type            => VType

    case Pi(x, i, t, b) => VPi(x, i, eval(t), Clos(b))
    case Lam(x, i, b)   => VLam(x, i, Clos(b))
    case App(f, a, i)   => vapp(eval(f), eval(a), i)

    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))
    case Pair(a, b)     => VPair(eval(a), eval(b))
    case Proj(t, p)     => vproj(eval(t), p)

    case Wk(tm) => eval(tm)(env.tail)

    case Meta(id)         => vmeta(id)
    case AppPruning(t, p) => vappPruning(eval(t), p)

  // quotation
  enum Unfold:
    case UnfoldAll
    case UnfoldMetas
  export Unfold.*

  @tailrec
  def force(v: Val, unfold: Unfold = UnfoldAll): Val = v match
    case VFlex(id, sp) =>
      getMeta(id) match
        case Solved(v, _) => force(vspine(v, sp), unfold)
        case Unsolved(_)  => v
    case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case _                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj)

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VType             => Type
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)     => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, _) => quote(Global(x), sp, unfold)

      case VLam(x, i, b) => Lam(x, i, quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)
