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

  extension (c: Clos2)
    def apply(v: Val, w: Val): Val = c match
      case CClos2(env, tm) => eval(tm)(w :: v :: env)
      case CFun2(f)        => f(v, w)

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

  def eval(s: Stage[Ty])(implicit env: Env): Stage[VTy] = s match
    case S1     => S1
    case S0(vf) => S0(eval(vf))

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Var(ix)            => env(ix.expose)
    case Global(x)          => vglobal(x)
    case Prim(x)            => vprim(x)
    case Let(_, _, _, v, b) => eval(b)(eval(v) :: env)
    case U(s)               => VU(eval(s))

    case Pi(x, i, t, b)   => VPi(x, i, eval(t), Clos(b))
    case FunTy(t, vf, b)  => VFunTy(eval(t), eval(vf), eval(b))
    case Lam(x, i, b)     => VLam(x, i, Clos(b))
    case App(f, a, i)     => vapp(eval(f), eval(a), i)
    case Fix(go, x, b, a) => VFix(go, x, CClos2(env, b), eval(a))

    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))
    case PairTy(t, b)   => VPairTy(eval(t), eval(b))
    case Pair(a, b)     => VPair(eval(a), eval(b))
    case Proj(t, p)     => vproj(eval(t), p)

    case IntLit(n) => VIntLit(n)

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
      case SSplice(tm)      => quote(hd, tm, unfold).splice
      case SPrim(sp, x, args) =>
        val as = args.foldLeft(Prim(x)) { case (f, (a, i)) =>
          App(f, quote(a, unfold), i)
        }
        App(as, quote(hd, sp, unfold), Expl)

  private def quote(hd: Head)(implicit l: Lvl): Tm = hd match
    case HVar(ix) => Var(ix.toIx)
    case HPrim(x) => Prim(x)

  def quoteS(s: Stage[VTy], unfold: Unfold = UnfoldMetas)(implicit
      l: Lvl
  ): Stage[Ty] = s match
    case S1     => S1
    case S0(vf) => S0(quote(vf, unfold))

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)     => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, _) => quote(Global(x), sp, unfold)
      case VU(s)             => U(quoteS(s, unfold))

      case VLam(x, i, b) => Lam(x, i, quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VFunTy(t, vf, b) =>
        FunTy(quote(t, unfold), quote(vf, unfold), quote(b, unfold))
      case VFix(go, x, b, a) =>
        Fix(
          go,
          x,
          quote(b(VVar(l), VVar(l + 1)), unfold)(l + 2),
          quote(a, unfold)
        )

      case VPair(fst, snd) => Pair(quote(fst, unfold), quote(snd, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VPairTy(t, b) => PairTy(quote(t, unfold), quote(b, unfold))

      case VIntLit(n) => IntLit(n)

      case VLift(vf, t) => Lift(quote(vf, unfold), quote(t, unfold))
      case VQuote(t)    => quote(t, unfold).quote

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)

  def primType(x: PrimName): (VTy, Stage[VTy]) = x match
    case PVF => (VMetaTy(), S1)
    case PV  => (VVF(), S1)
    case PF  => (VVF(), S1)

    case PVoid => (VTyV(), S1)
    // {A : Meta} -> ^Void -> A
    case PAbsurd =>
      (
        vpiI(
          "A",
          VU(S1),
          a => vpi("_", VLift(VV(), VVoid()), _ => a)
        ),
        S1
      )

    case PUnitType => (VTyV(), S1)
    case PUnit     => (VUnitType(), S0(VV()))

    case PBool  => (VTyV(), S1)
    case PTrue  => (VBool(), S0(VV()))
    case PFalse => (VBool(), S0(VV()))
    // {vf : VF} {A : Ty vf} -> ^Bool -> ^A -> ^A -> ^A
    case PCaseBool =>
      (
        vpiI(
          "vf",
          VVF(),
          vf =>
            vpiI(
              "A",
              VU(S0(vf)),
              a =>
                vfun(
                  VLift(VV(), VBool()),
                  vfun(VLift(vf, a), vfun(VLift(vf, a), VLift(vf, a)))
                )
            )
        ),
        S1
      )

    case PInt => (VTyV(), S1)
    case PPrimIntAdd =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VInt())), S0(VF()))
    case PPrimIntMul =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VInt())), S0(VF()))
    case PPrimIntSub =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VInt())), S0(VF()))
    case PPrimIntDiv =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VInt())), S0(VF()))
    case PPrimIntMod =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VInt())), S0(VF()))
    case PPrimIntEq =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VBool())), S0(VF()))
    case PPrimIntNeq =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VBool())), S0(VF()))
    case PPrimIntGt =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VBool())), S0(VF()))
    case PPrimIntLt =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VBool())), S0(VF()))
    case PPrimIntGeq =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VBool())), S0(VF()))
    case PPrimIntLeq =>
      (VFunTy(VInt(), VF(), VFunTy(VInt(), VV(), VBool())), S0(VF()))

    // Ty V -> Ty V
    case PList => (vfun(VU(S0(VV())), VU(S0(VV()))), S1)
    // {A : Ty V} -> ^(List A)
    case PNil => (vpiI("A", VU(S0(VV())), a => VLift(VV(), VList(a))), S1)
    // {A : Ty V} -> ^A -> ^(List A) -> ^(List A)
    case PCons =>
      (
        vpiI(
          "A",
          VU(S0(VV())),
          a =>
            vfun(
              VLift(VV(), a),
              vfun(VLift(VV(), VList(a)), VLift(VV(), VList(a)))
            )
        ),
        S1
      )
    // {A : Ty V} {vf : VF} {R : Ty vf} -> ^(List A) -> ^R -> (^A -> ^(List A) -> ^R) -> ^R
    case PCaseList =>
      (
        vpiI(
          "A",
          VU(S0(VV())),
          a =>
            vpiI(
              "vf",
              VVF(),
              vf =>
                vpiI(
                  "R",
                  VU(S0(vf)),
                  r =>
                    vfun(
                      VLift(VV(), VList(a)),
                      vfun(
                        VLift(vf, r),
                        vfun(
                          vfun(
                            VLift(VV(), a),
                            vfun(VLift(VV(), VList(a)), VLift(vf, r))
                          ),
                          VLift(vf, r)
                        )
                      )
                    )
                )
            )
        ),
        S1
      )
