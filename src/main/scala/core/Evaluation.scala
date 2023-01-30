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
    case VLam(_, _, _, b) => b(a)
    case VRigid(hd, sp)   => VRigid(hd, SApp(sp, a, i))
    case VFlex(hd, sp)    => VFlex(hd, SApp(sp, a, i))
    case VGlobal(uri, sp, v) =>
      VGlobal(uri, SApp(sp, a, i), () => vapp(v(), a, i))
    case _ => impossible()

  def vappE(f: Val, a: Val): Val = vapp(f, a, Expl)
  def vappI(f: Val, a: Val): Val = vapp(f, a, Impl)

  def vproj(v: Val, p: ProjType): Val = v match
    case VPair(fst, snd, _) =>
      p match
        case Fst         => fst
        case Snd         => snd
        case Named(_, 0) => fst
        case Named(x, i) => vproj(snd, Named(x, i - 1))
    case VRigid(hd, sp) => VRigid(hd, SProj(sp, p))
    case VFlex(hd, sp)  => VFlex(hd, SProj(sp, p))
    case VGlobal(uri, sp, v) =>
      VGlobal(uri, SProj(sp, p), () => vproj(v(), p))
    case _ => impossible()

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
      case (_, VRigid(hd, sp), _) => VRigid(hd, SPrim(sp, x, as))
      case (_, VFlex(hd, sp), _)  => VFlex(hd, SPrim(sp, x, as))
      case (_, VGlobal(y, sp, v), _) =>
        VGlobal(y, SPrim(sp, x, as), () => vprimelim(x, as, v()))
      case _ => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
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
    case _ => VPrim(x)

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Var(ix)               => env(ix.expose)
    case Global(x)             => vglobal(x)
    case Prim(x)               => vprim(x)
    case Let(_, _, _, _, v, b) => eval(b)(eval(v) :: env)
    case U(s)                  => VU(s.map(eval))

    case Pi(x, i, t, b)   => VPi(x, i, eval(t), Clos(b))
    case Lam(x, i, ty, b) => VLam(x, i, eval(ty), Clos(b))
    case App(f, a, i)     => vapp(eval(f), eval(a), i)

    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))
    case Pair(a, b, ty) => VPair(eval(a), eval(b), eval(ty))
    case Proj(t, p, _)  => vproj(eval(t), p)

    case IntLit(n) => VIntLit(n)

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
    case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case _                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj)  => Proj(quote(hd, tm, unfold), proj, Irrelevant)
      case SSplice(tm)      => quote(hd, tm, unfold).splice
      case SPrim(sp, x, args) =>
        val as = args.foldLeft(Prim(x)) { case (f, (a, i)) =>
          App(f, quote(a, unfold), i)
        }
        App(as, quote(hd, sp, unfold), Expl)

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)
    case HPrim(x) => Prim(x)

  def quoteS(s: VStage, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): CStage =
    s.map(v => quote(v, unfold))

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)     => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, _) => quote(Global(x), sp, unfold)
      case VU(s)             => U(quoteS(s))

      case VLam(x, i, ty, b) =>
        Lam(x, i, quote(ty, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VPair(fst, snd, t) =>
        Pair(quote(fst, unfold), quote(snd, unfold), quote(t, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VIntLit(n) => IntLit(n)

      case VLift(vf, t) => Lift(quote(vf, unfold), quote(t, unfold))
      case VQuote(t)    => quote(t, unfold).quote

      case VIrrelevant => Irrelevant

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)

  def primType(x: PrimName): (VTy, VStage) = x match
    case PVF  => (VUMeta(), SMeta)
    case PVal => (VVF(), SMeta)
    case PFun => (VVF(), SMeta)

    // Ty Val -> {vf : VF} -> Ty vf -> Ty Fun
    case PTFun =>
      (vfun(VVTy(), vpiI("vf", VVF(), vf => vfun(VUTy(vf), VFTy()))), SMeta)
    // Ty Val -> Ty Val -> Ty Val
    case PTPair => (vfun(VVTy(), vfun(VVTy(), VVTy())), SMeta)

    // {A : Ty Val} -> {vf : VF} -> {B : Ty vf} -> ((^A -> ^B) -> ^A -> ^B) -> ^(A -> B)
    case PFix =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "vf",
              VVF(),
              vf =>
                vpiI(
                  "B",
                  VUTy(vf),
                  b =>
                    val f = vfun(VLift(VVal(), a), VLift(vf, b))
                    vfun(vfun(f, f), VLift(VFun(), VTFun(a, vf, b)))
                )
            )
        ),
        SMeta
      )

    case PUnitType => (VVTy(), SMeta)
    case PUnit     => (VUnitType(), SVTy())

    case PBool  => (VVTy(), SMeta)
    case PTrue  => (VBool(), SVTy())
    case PFalse => (VBool(), SVTy())
    // {vf : VF} -> {A : Ty vf} -> ^Bool -> ^A -> ^A -> ^A
    case PCaseBool =>
      (
        vpiI(
          "vf",
          VVF(),
          vf =>
            vpiI(
              "A",
              VUTy(vf),
              a =>
                val qa = VLift(vf, a)
                vfun(VLift(VVal(), VBool()), vfun(qa, vfun(qa, qa)))
            )
        ),
        SMeta
      )

    case PInt => (VVTy(), SMeta)
    case PIntLeq =>
      (VTFun(VInt(), VFun(), VTFun(VInt(), VVal(), VBool())), SFTy())
    case PIntSub =>
      (VTFun(VInt(), VFun(), VTFun(VInt(), VVal(), VInt())), SFTy())
    case PIntMul =>
      (VTFun(VInt(), VFun(), VTFun(VInt(), VVal(), VInt())), SFTy())
