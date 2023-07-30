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
    case VGlobal(x, sp, v) =>
      VGlobal(x, SApp(sp, a, i), () => vapp(v(), a, i))
    case f => impossible()

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
    case VGlobal(x, sp, v) =>
      VGlobal(x, SProj(sp, p), () => vproj(v(), p))
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
      case (PEqLabel, VStringLit(a), List((VStringLit(b), _))) =>
        if a == b then
          vlam("R", VUMeta(), r => vlam("t", r, t => vlam("f", r, f => t)))
        else vlam("R", VUMeta(), r => vlam("t", r, t => vlam("f", r, f => f)))
      case (PAppendLabel, VStringLit(""), List((b, _))) => b
      case (PAppendLabel, _, List((VStringLit(""), _))) => v
      case (PAppendLabel, VStringLit(a), List((VStringLit(b), _))) =>
        VStringLit(a + b)

      case (_, VRigid(hd, sp), _) => VRigid(hd, SPrim(sp, x, as))
      case (_, VFlex(hd, sp), _)  => VFlex(hd, SPrim(sp, x, as))
      case (_, VGlobal(y, sp, v), _) =>
        VGlobal(y, SPrim(sp, x, as), () => vprimelim(x, as, v()))
      case _ => impossible()

  private def vmatch(
      dty: VTy,
      rty: VTy,
      cs: List[(Name, Int, Val)],
      o: Option[Val],
      v: Val
  ): Val =
    v match
      case VRigid(hd, sp) => VRigid(hd, SMatch(sp, dty, rty, cs, o))
      case VFlex(hd, sp)  => VFlex(hd, SMatch(sp, dty, rty, cs, o))
      case VGlobal(y, sp, v) =>
        VGlobal(
          y,
          SMatch(sp, dty, rty, cs, o),
          () => vmatch(dty, rty, cs, o, v())
        )
      case _ => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId                         => v
    case SApp(sp, a, i)              => vapp(vspine(v, sp), a, i)
    case SSplice(sp)                 => vsplice(vspine(v, sp))
    case SProj(sp, proj)             => vproj(vspine(v, sp), proj)
    case SPrim(sp, x, as)            => vprimelim(x, as, vspine(v, sp))
    case SMatch(sp, dty, rty, cs, o) => vmatch(dty, rty, cs, o, vspine(v, sp))

  private def vmeta(id: MetaId): Val = getMeta(id) match
    case Solved(_, v, _, _)   => v
    case Unsolved(_, _, _, _) => VMeta(id)

  def vappPruning(v: Val, p: Pruning)(implicit env: Env): Val =
    (env, p) match
      case (Nil, Nil)               => v
      case (a :: env, Some(i) :: p) => vapp(vappPruning(v, p)(env), a, i)
      case (_ :: env, None :: p)    => vappPruning(v, p)(env)
      case _                        => impossible()

  private def vprim(x: PrimName): Val = x match
    case PEqLabel =>
      vlam(
        "a",
        VIrrelevant,
        a =>
          vlam("b", VIrrelevant, b => vprimelim(PEqLabel, List((b, Expl)), a))
      )
    case PAppendLabel =>
      vlam(
        "a",
        VIrrelevant,
        a =>
          vlam(
            "b",
            VIrrelevant,
            b => vprimelim(PAppendLabel, List((b, Expl)), a)
          )
      )
    case _ => VPrim(x)

  def eval(tm: Tm)(implicit env: Env): Val = tm match
    case Var(ix)                  => env(ix.expose)
    case Global(x)                => vglobal(x)
    case Prim(x)                  => vprim(x)
    case Let(_, _, _, _, _, v, b) => eval(b)(eval(v) :: env)
    case U(s)                     => VU(s.map(eval))

    case IntLit(v)    => VIntLit(v)
    case StringLit(v) => VStringLit(v)

    case Pi(u, x, i, t, b) => VPi(u, x, i, eval(t), Clos(b))
    case Lam(x, i, ty, b)  => VLam(x, i, eval(ty), Clos(b))
    case App(f, a, i)      => vapp(eval(f), eval(a), i)
    case Fix(ty, rty, g, x, b, arg) =>
      VFix(eval(ty), eval(rty), g, x, CClos2(env, b), eval(arg))

    case Sigma(x, t, b)   => VSigma(x, eval(t), Clos(b))
    case Pair(a, b, ty)   => VPair(eval(a), eval(b), eval(ty))
    case Proj(t, p, _, _) => vproj(eval(t), p)

    case Lift(cv, t) => VLift(eval(cv), eval(t))
    case Quote(t)    => vquote(eval(t))
    case Splice(t)   => vsplice(eval(t))

    case Foreign(rt, cmd, as) =>
      VForeign(eval(rt), eval(cmd), as.map((a, t) => (eval(a), eval(t))))

    case TCon(x, as)         => VTCon(x, as.map(eval))
    case Con(x, cx, tas, as) => VCon(x, cx, tas.map(eval), as.map(eval))
    case Match(dty, rty, scrut, cs, other) =>
      vmatch(
        eval(dty),
        eval(rty),
        cs.map((x, i, b) => (x, i, eval(b))),
        other.map(eval),
        eval(scrut)
      )

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
        case Solved(_, v, _, _)   => force(vspine(v, sp), unfold)
        case Unsolved(_, _, _, _) => v
    case VGlobal(_, _, v) if unfold == UnfoldAll => force(v(), UnfoldAll)
    case _                                       => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj) =>
        Proj(quote(hd, tm, unfold), proj, Irrelevant, Irrelevant)
      case SSplice(tm) => quote(hd, tm, unfold).splice
      case SPrim(sp, x, args) =>
        val as = args.foldLeft(Prim(x)) { case (f, (a, i)) =>
          App(f, quote(a, unfold), i)
        }
        App(as, quote(hd, sp, unfold), Expl)
      case SMatch(sp, dty, rty, cs, other) =>
        val qcs = cs.map((x, i, b) => (x, i, quote(b, unfold)))
        Match(
          quote(dty, unfold),
          quote(rty, unfold),
          quote(hd, sp, unfold),
          qcs,
          other.map(quote(_, unfold))
        )

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

      case VIntLit(v)    => IntLit(v)
      case VStringLit(v) => StringLit(v)

      case VLam(x, i, ty, b) =>
        Lam(x, i, quote(ty, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VPi(u, x, i, t, b) =>
        Pi(u, x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VFix(ty, rty, g, x, b, arg) =>
        Fix(
          quote(ty, unfold),
          quote(rty, unfold),
          g,
          x,
          quote(b(VVar(l), VVar(l + 1)), unfold)(l + 2),
          quote(arg, unfold)
        )

      case VPair(fst, snd, t) =>
        Pair(quote(fst, unfold), quote(snd, unfold), quote(t, unfold))
      case VSigma(x, t, b) =>
        Sigma(x, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))

      case VLift(cv, t) => Lift(quote(cv, unfold), quote(t, unfold))
      case VQuote(t)    => quote(t, unfold).quote

      case VTCon(x, as) => TCon(x, as.map(a => quote(a, unfold)))
      case VCon(x, cx, tas, as) =>
        Con(
          x,
          cx,
          tas.map(a => quote(a, unfold)),
          as.map(a => quote(a, unfold))
        )

      case VForeign(rt, cmd, as) =>
        Foreign(
          quote(rt, unfold),
          quote(cmd, unfold),
          as.map((a, t) => (quote(a, unfold), quote(t, unfold)))
        )

      case VIrrelevant => Irrelevant

  def nf(tm: Tm)(implicit l: Lvl = lvl0, env: Env = Nil): Tm =
    quote(eval(tm), UnfoldAll)

  def primType(x: PrimName): (VTy, VStage) = x match
    case PCV   => (VUMeta(), SMeta)
    case PVal  => (VCV(), SMeta)
    case PComp => (VCV(), SMeta)

    // Ty Val -> {cv : CV} -> Ty cv -> Ty Comp
    case PFun =>
      (vfun(VVTy(), vpiI("cv", VCV(), cv => vfun(VUTy(cv), VCTy()))), SMeta)

    case PUnitType => (VUMeta(), SMeta)
    case PUnit     => (VUnitType(), SMeta)

    case PIO => (vfun(VVTy(), VCTy()), SMeta)
    // returnIO : {A : VTy} -> ^A -> ^(IO A)
    case PReturnIO =>
      (
        vpiI(
          "A",
          VVTy(),
          a => vfun(VLift(VVal(), a), VLift(VComp(), vappE(VPrim(PIO), a)))
        ),
        SMeta
      )
    // bindIO : {A B : VTy} -> ^(IO A) -> (^A -> ^(IO B)) -> ^(IO B)
    case PBindIO =>
      def vio(a: VTy) = VLift(VComp(), vappE(VPrim(PIO), a))
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "B",
              VVTy(),
              b => vfun(vio(a), vfun(vfun(VLift(VVal(), a), vio(b)), vio(b)))
            )
        ),
        SMeta
      )

    case PLabel       => (VUMeta(), SMeta)
    case PEqLabel     => (vfun(VLabel(), vfun(VLabel(), vcbool)), SMeta)
    case PAppendLabel => (vfun(VLabel(), vfun(VLabel(), VLabel())), SMeta)

    // Label -> VTy
    case PForeignType => (vfun(VLabel(), VVTy()), SMeta)

    case PNew => (VUMeta(), SMeta)
    // (1 _ : New) -> ()
    case PNewDrop => (vfun1(VNew(), VUnitType()), SMeta)
    // {cv : CV} {A : Ty cv} (1 _ : {R : Meta} -> (^A -> R) -> (1 _ : New) -> R) -> ^A
    case PNewScope =>
      (
        vpiI(
          "cv",
          VCV(),
          cv =>
            vpiI(
              "A",
              VUTy(cv),
              a =>
                vfun1(
                  vpiI(
                    "R",
                    VUMeta(),
                    r => vfun(vfun(VLift(cv, a), r), vfun1(VNew(), r))
                  ),
                  VLift(cv, a)
                )
            )
        ),
        SMeta
      )

    // Label -> VTy
    case PRW => (vfun(VLabel(), VUMeta()), SMeta)

  // (R : Meta) -> R -> R -> R
  val vcbool: Val = vpi("R", VUMeta(), r => vfun(r, vfun(r, r)))
