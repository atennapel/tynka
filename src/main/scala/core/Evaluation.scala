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
    case U(s)                  => VU(s)

    case Pi(x, i, t, b)      => VPi(x, i, eval(t), Clos(b))
    case Lam(x, i, ty, b)    => VLam(x, i, eval(ty), Clos(b))
    case App(f, a, i)        => vapp(eval(f), eval(a), i)
    case Fix(go, x, t, b, a) => VFix(go, x, eval(t), CClos2(env, b), eval(a))

    case Sigma(x, t, b) => VSigma(x, eval(t), Clos(b))
    case Pair(a, b, ty) => VPair(eval(a), eval(b), eval(ty))
    case Proj(t, p, _)  => vproj(eval(t), p)

    case IntLit(n) => VIntLit(n)

    case Lift(t)   => VLift(eval(t))
    case Quote(t)  => vquote(eval(t))
    case Splice(t) => vsplice(eval(t))

    case Wk(tm)     => eval(tm)(env.tail)
    case Irrelevant => VIrrelevant

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

  def quote(v: Val, unfold: Unfold = UnfoldMetas)(implicit l: Lvl): Tm =
    force(v, unfold) match
      case VRigid(hd, sp)    => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)     => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, _) => quote(Global(x), sp, unfold)
      case VU(s)             => U(s)

      case VLam(x, i, ty, b) =>
        Lam(x, i, quote(ty, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VPi(x, i, t, b) =>
        Pi(x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VFix(go, x, t, b, a) =>
        Fix(
          go,
          x,
          quote(t, unfold),
          quote(b(VVar(l), VVar(l + 1)), unfold)(l + 2),
          quote(a, unfold)
        )

      case VPair(fst, snd, t) =>
        Pair(quote(fst, unfold), quote(snd, unfold), quote(t, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VIntLit(n) => IntLit(n)

      case VLift(t)  => Lift(quote(t, unfold))
      case VQuote(t) => quote(t, unfold).quote

      case VIrrelevant => Irrelevant

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)

  def primType(x: PrimName): (VTy, Stage) = x match
    case PVTy => (VU(SMeta), SMeta)
    // ValTy -> Ty
    case PVal => (vfun(VVTy(), VTy()), SMeta)
    // ValTy -> Ty -> Ty
    case PFun => (vfun(VVTy(), vfun(VTy(), VTy())), SMeta)
    // VTy -> VTy -> VTy
    case PPair => (vfun(VVTy(), vfun(VVTy(), VVTy())), SMeta)

    case PVoid => (VVTy(), SMeta)
    // {A : ValTy} -> ^(Val Void) -> ^(Val A)
    case PAbsurd =>
      (
        vpiI(
          "A",
          VVTy(),
          a => vpi("_", VLift(VVal(VVoid())), _ => VLift(VVal(a)))
        ),
        SMeta
      )

    case PUnitType => (VVTy(), SMeta)
    case PUnit     => (VVal(VUnitType()), STy)

    case PBool  => (VVTy(), SMeta)
    case PTrue  => (VVal(VBool()), STy)
    case PFalse => (VVal(VBool()), STy)
    // {A : ValTy} -> ^(Val Bool) -> ^(Val A) -> ^(Val A) -> ^(Val A)
    case PCaseBool =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vfun(
              VLift(VVal(VBool())),
              vfun(VLift(VVal(a)), vfun(VLift(VVal(a)), VLift(VVal(a))))
            )
        ),
        SMeta
      )

    case PInt => (VVTy(), SMeta)
    // Fun Int (Fun Int (Val Int))
    case PPrimIntAdd => (VFun(VInt(), VFun(VInt(), VVal(VInt()))), STy)
    case PPrimIntMul => (VFun(VInt(), VFun(VInt(), VVal(VInt()))), STy)
    case PPrimIntSub => (VFun(VInt(), VFun(VInt(), VVal(VInt()))), STy)
    case PPrimIntDiv => (VFun(VInt(), VFun(VInt(), VVal(VInt()))), STy)
    case PPrimIntMod => (VFun(VInt(), VFun(VInt(), VVal(VInt()))), STy)

    case PPrimIntEq  => (VFun(VInt(), VFun(VInt(), VVal(VBool()))), STy)
    case PPrimIntNeq => (VFun(VInt(), VFun(VInt(), VVal(VBool()))), STy)
    case PPrimIntGt  => (VFun(VInt(), VFun(VInt(), VVal(VBool()))), STy)
    case PPrimIntLt  => (VFun(VInt(), VFun(VInt(), VVal(VBool()))), STy)
    case PPrimIntGeq => (VFun(VInt(), VFun(VInt(), VVal(VBool()))), STy)
    case PPrimIntLeq => (VFun(VInt(), VFun(VInt(), VVal(VBool()))), STy)

    // ValTy -> ValTy
    case PList => (vfun(VVTy(), VVTy()), SMeta)
    // {A : ValTy} -> ^(Val (List A))
    case PNil => (vpiI("A", VVTy(), a => VLift(VVal(VList(a)))), SMeta)
    // {A : ValTy} -> ^(Val A) -> ^(Val (List A)) -> ^(Val (List A))
    case PCons =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vfun(
              VLift(VVal(a)),
              vfun(VLift(VVal(VList(a))), VLift(VVal(VList(a))))
            )
        ),
        SMeta
      )
    // {A : ValTy} {R : ValTy} -> ^(Val (List A)) -> ^(Val R) -> (^(Val A) -> ^(Val (List A)) -> ^(Val R)) -> ^(Val R)
    case PCaseList =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "R",
              VVTy(),
              r =>
                vfun(
                  VLift(VVal(VList(a))),
                  vfun(
                    VLift(VVal(r)),
                    vfun(
                      vfun(
                        VLift(VVal(a)),
                        vfun(VLift(VVal(VList(a))), VLift(VVal(r)))
                      ),
                      VLift(VVal(r))
                    )
                  )
                )
            )
        ),
        SMeta
      )

    // ValTy -> ValTy -> ValTy
    case PEither => (vfun(VVTy(), vfun(VVTy(), VVTy())), SMeta)
    // {A : ValTy} {B : ValTy} -> ^(Val A) -> ^(Val (Either A B))
    case PLeft =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "B",
              VVTy(),
              b => vfun(VLift(VVal(a)), VLift(VVal(VEither(a, b))))
            )
        ),
        SMeta
      )
    // {A : ValTy} {B : ValTy} -> ^(Val B) -> ^(Val (Either A B))
    case PRight =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "B",
              VVTy(),
              b => vfun(VLift(VVal(b)), VLift(VVal(VEither(a, b))))
            )
        ),
        SMeta
      )
    // {A : ValTy} {B : ValTy} {R : ValTy} -> ^(Val (Either A B)) -> (^(Val A) -> ^(Val R)) -> (^(Val B) -> ^(Val R)) -> ^(Val R)
    case PCaseEither =>
      val tv = VVTy()
      def l(v: VTy): VTy = VLift(VVal(v))
      (
        vpiI(
          "A",
          tv,
          a =>
            vpiI(
              "B",
              tv,
              b =>
                vpiI(
                  "R",
                  tv,
                  r =>
                    vfun(
                      l(VEither(a, b)),
                      vfun(
                        vfun(l(a), l(r)),
                        vfun(vfun(l(b), l(r)), l(r))
                      )
                    )
                )
            )
        ),
        SMeta
      )
