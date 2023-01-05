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

  def vappE(f: Val, a: Val): Val = vapp(f, a, Expl)
  def vappI(f: Val, a: Val): Val = vapp(f, a, Impl)

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

  def vquote(v: Val): Val = v match
    case VRigid(hd, SSplice(sp))     => VRigid(hd, sp)
    case VFlex(hd, SSplice(sp))      => VFlex(hd, sp)
    case VGlobal(hd, SSplice(sp), v) => VGlobal(hd, sp, () => vquote(v()))
    case v                           => VQuote(v)

  def vsplice(v: Val): Val = v match
    case VQuote(v)         => v
    case VRigid(hd, sp)    => VRigid(hd, SSplice(sp))
    case VFlex(hd, sp)     => VFlex(hd, SSplice(sp))
    case VGlobal(x, sp, v) => VGlobal(x, SSplice(sp), () => vsplice(v()))
    case _                 => impossible()

  private def vprimelim(x: PrimName, as: List[(Val, Icit)], v: Val): Val =
    (x, force(v), as) match
      // case (PElimBool, VTrue(), List(_, (t, _), _))  => t
      // case (PElimBool, VFalse(), List(_, _, (f, _))) => f

      case (_, VRigid(hd, sp), _) => VRigid(hd, SPrim(sp, x, as))
      case (_, VFlex(hd, sp), _)  => VFlex(hd, SPrim(sp, x, as))
      case (_, VGlobal(y, sp, v), _) =>
        VGlobal(y, SPrim(sp, x, as), () => vprimelim(x, as, v()))
      case _ => impossible()

  private def vspine(v: Val, sp: Spine): Val = sp match
    case SId              => v
    case SApp(sp, a, i)   => vapp(vspine(v, sp), a, i)
    case SSplice(sp)      => vsplice(vspine(v, sp))
    case SProj(sp, proj)  => vproj(vspine(v, sp), proj)
    case SPrim(sp, x, as) => vprimelim(x, as, vspine(v, sp))

  private def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(v, _, _) => v
    case Unsolved(_, _)  => VMeta(id)

  def vappPruning(v: Val, p: Pruning)(implicit env: Env): Val =
    (env, p) match
      case (Nil, Nil)               => v
      case (a :: env, Some(i) :: p) => vapp(vappPruning(v, p)(env), a, i)
      case (_ :: env, None :: p)    => vappPruning(v, p)(env)
      case _                        => impossible()

  private def vprim(x: PrimName): Val = x match
    // \{A} v. absurd {A} v
    /*case PAbsurd =>
      vlamI("A", a => vlam("v", v => vprimelim(PAbsurd, List((a, Impl)), v)))
    // \P t f b. elimBool P t f b
    case PElimBool =>
      vlam(
        "P",
        p =>
          vlam(
            "t",
            t =>
              vlam(
                "f",
                f =>
                  vlam(
                    "b",
                    b =>
                      vprimelim(
                        PElimBool,
                        List((p, Expl), (t, Expl), (f, Expl)),
                        b
                      )
                  )
              )
          )
      )*/
    case _ => VPrim(x)

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Var(ix)         => env(ix.expose)
    case Global(x)       => vglobal(x)
    case Prim(x)         => vprim(x)
    case Let(_, _, v, b) => eval(b)(eval(v) :: env)

    case Pi(x, i, t, b) => VPi(x, i, eval(t), Clos(b))
    case Lam(x, i, b)   => VLam(x, i, Clos(b))
    case App(f, a, i)   => vapp(eval(f), eval(a), i)

    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))
    case Pair(a, b)     => VPair(eval(a), eval(b))
    case Proj(t, p)     => vproj(eval(t), p)

    case Lift(vf, t) => VLift(eval(vf), eval(t))
    case Quote(t)    => vquote(eval(t))
    case Splice(t)   => vsplice(eval(t))

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
        case Solved(v, _, _) => force(vspine(v, sp), unfold)
        case Unsolved(_, _)  => v
    case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case _                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj)
      case SSplice(tm)      => Splice(quote(hd, tm, unfold))
      case SPrim(sp, x, args) =>
        val as = args.foldLeft(Prim(x)) { case (f, (a, i)) =>
          App(f, quote(a, unfold), i)
        }
        App(as, quote(hd, sp, unfold), Expl)

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)
    case HPrim(x) => Prim(x)

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)     => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, _) => quote(Global(x), sp, unfold)

      case VLam(x, i, b) => Lam(x, i, quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VLift(vf, t) => Lift(quote(vf, unfold), quote(t, unfold))
      case VQuote(t)    => Quote(quote(t, unfold))

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)

  def primType(x: PrimName): (VTy, VUniv) = x match
    case PMeta => (VMetaTy(), VMetaTy())
    case PVF   => (VMetaTy(), VMetaTy())
    case PV    => (VVF(), VMetaTy())
    case PF    => (VVF(), VMetaTy())
    // VF -> Meta
    case PTy => (vfun(VVF(), VMetaTy()), VMetaTy())

    case PVoid => (VTyV(), VMetaTy())
    // {A : Type} -> Void -> A
    // case PAbsurd => vpiI("A", VType(), a => vpi("_", VVoid(), _ => a))

    case PUnitType => (VTyV(), VMetaTy())
    case PUnit     => (VUnitType(), VTyV())

    case PBool  => (VTyV(), VMetaTy())
    case PTrue  => (VBool(), VTyV())
    case PFalse => (VBool(), VTyV())
    // (P : Bool -> Type) -> P True -> P False -> (b : bool) -> P b
    /*case PElimBool =>
      vpi(
        "P",
        vfun(VBool(), VType()),
        p =>
          vfun(
            vappE(p, VTrue()),
            vfun(vappE(p, VFalse()), vpi("b", VBool(), b => vappE(p, b)))
          )
      )*/
