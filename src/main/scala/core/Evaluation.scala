package core

import common.Common.*
import Syntax.*
import Value.*
import Metas.*
import Globals.*

import scala.annotation.tailrec
import scala.runtime.VolatileIntRef

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
    val entry = getGlobal(x).get
    val value = entry.value
    VGlobal(x, SId, entry.opaque, () => value)

  def vapp(f: Val, a: Val, i: Icit): Val = f match
    case VLam(_, _, _, b) => b(a)
    case VRigid(hd, sp)   => VRigid(hd, SApp(sp, a, i))
    case VFlex(hd, sp)    => VFlex(hd, SApp(sp, a, i))
    case VGlobal(x, sp, opq, v) =>
      VGlobal(x, SApp(sp, a, i), opq, () => vapp(v(), a, i))
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
    case VGlobal(x, sp, opq, v) =>
      VGlobal(x, SProj(sp, p), opq, () => vproj(v(), p))
    case _ => impossible()

  def vfst(v: Val): Val = vproj(v, Fst)
  def vsnd(v: Val): Val = vproj(v, Snd)

  def vquote(v: Val): Val = v match
    case VRigid(hd, SSplice(sp)) => VRigid(hd, sp)
    case VFlex(hd, SSplice(sp))  => VFlex(hd, sp)
    case VGlobal(hd, SSplice(sp), opq, v) =>
      VGlobal(hd, sp, opq, () => vquote(v()))
    case v => VQuote(v)

  def vsplice(v: Val): Val = v match
    case VQuote(v)      => v
    case VRigid(hd, sp) => VRigid(hd, SSplice(sp))
    case VFlex(hd, sp)  => VFlex(hd, SSplice(sp))
    case VGlobal(x, sp, opq, v) =>
      VGlobal(x, SSplice(sp), opq, () => vsplice(v()))
    case _ => impossible()

  private def vprimelim(
      x: PrimName,
      i: Int,
      as: List[(Val, Icit)],
      v: Val
  ): Val =
    (x, force(v), as.map((v, i) => (force(v), i))) match
      case (PEqLabel, VStringLit(a), List((VStringLit(b), _))) =>
        if a == b then
          vlam("R", VUMeta(), r => vlam("t", r, t => vlam("f", r, f => t)))
        else vlam("R", VUMeta(), r => vlam("t", r, t => vlam("f", r, f => f)))
      case (PEqLabel, VStringLit(_), List((a, _))) =>
        vprimelim(PEqLabel, 1 - i, List((v, Expl)), a)

      case (PAppendLabel, VStringLit(""), List((b, _))) => b
      case (PAppendLabel, _, List((VStringLit(""), _))) => v
      case (PAppendLabel, VStringLit(a), List((VStringLit(b), _))) =>
        VStringLit(a + b)
      case (PAppendLabel, VStringLit(_), List((a, _))) =>
        vprimelim(PAppendLabel, 1 - i, List((v, Expl)), a)

      case (
            PConHasIndex,
            VStringLit(c),
            List((VStringLit(i), _))
          ) =>
        (i.toIntOption, getGlobalCon(Name(c))) match
          case (Some(i), Some(e)) if i >= 0 && i < e._2.size => VUnitType()
          case _                                             => vcvoid
      case (PConHasIndex, VStringLit(_), List((a, _))) =>
        vprimelim(PConHasIndex, 1 - i, List((v, Expl)), a)

      case (
            PConParamType,
            VTCon(x, ps),
            List((VStringLit(c), _), (VStringLit(i), _))
          ) =>
        (getGlobalCon(Name(c)), i.toIntOption) match
          case (Some(e), Some(i)) if i >= 0 && i < e._2.size =>
            eval(e._2(i))(ps.reverse)
          case _ => vcvoid
      case (PConParamType, VTCon(_, _), List((c, _), (i, _))) =>
        (c, i) match
          case (VFlex(_, _), _) =>
            vprimelim(PConParamType, 1, List((v, Expl), (i, Expl)), c)
          case _ => vprimelim(PConParamType, 2, List((v, Expl), (c, Expl)), i)
      case (PConParamType, VStringLit(_), List((a, _), (cOri, _))) =>
        if i == 1 then
          vprimelim(PConParamType, 2, List((a, Expl), (v, Expl)), cOri)
        else vprimelim(PConParamType, 0, List((cOri, Expl), (v, Expl)), a)

      case (_, VRigid(hd, sp), _) => VRigid(hd, SPrim(sp, x, i, as))
      case (_, VFlex(hd, sp), _)  => VFlex(hd, SPrim(sp, x, i, as))
      case (_, VGlobal(y, sp, opq, v), _) =>
        VGlobal(y, SPrim(sp, x, i, as), opq, () => vprimelim(x, i, as, v()))
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
      case VGlobal(y, sp, opq, v) =>
        VGlobal(
          y,
          SMatch(sp, dty, rty, cs, o),
          opq,
          () => vmatch(dty, rty, cs, o, v())
        )
      case _ => impossible()

  def vspine(v: Val, sp: Spine): Val = sp match
    case SId                         => v
    case SApp(sp, a, i)              => vapp(vspine(v, sp), a, i)
    case SSplice(sp)                 => vsplice(vspine(v, sp))
    case SProj(sp, proj)             => vproj(vspine(v, sp), proj)
    case SPrim(sp, x, i, as)         => vprimelim(x, i, as, vspine(v, sp))
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
          vlam(
            "b",
            VIrrelevant,
            b => vprimelim(PEqLabel, 0, List((b, Expl)), a)
          )
      )
    case PAppendLabel =>
      vlam(
        "a",
        VIrrelevant,
        a =>
          vlam(
            "b",
            VIrrelevant,
            b => vprimelim(PAppendLabel, 0, List((b, Expl)), a)
          )
      )
    case PConHasIndex =>
      vlam(
        "C",
        VIrrelevant,
        c =>
          vlam(
            "i",
            VIrrelevant,
            i => vprimelim(PConHasIndex, 0, List((i, Expl)), c)
          )
      )
    case PConParamType =>
      vlam(
        "A",
        VIrrelevant,
        a =>
          vlam(
            "C",
            VIrrelevant,
            c =>
              vlam(
                "i",
                VIrrelevant,
                i => vprimelim(PConParamType, 0, List((c, Expl), (i, Expl)), a)
              )
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
    case Fun(u, a, b, c)   => VFun(u, eval(a), eval(b), eval(c))
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

    case Foreign(io, rt, cmd, as) =>
      VForeign(io, eval(rt), eval(cmd), as.map((a, t) => (eval(a), eval(t))))

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
  def force(v: Val, unfold: Unfold = UnfoldAll): Val =
    v match
      case VFlex(id, sp) =>
        getMeta(id) match
          case Solved(_, v, _, _)   => force(vspine(v, sp), unfold)
          case Unsolved(_, _, _, _) => v
      case VGlobal(_, _, opq, v) if !opq && unfold == UnfoldAll =>
        force(v(), UnfoldAll)
      case _ => v

  private def quote(hd: Tm, sp: Spine, unfold: Unfold)(implicit l: Lvl): Tm =
    sp match
      case SId              => hd
      case SApp(fn, arg, i) => App(quote(hd, fn, unfold), quote(arg, unfold), i)
      case SProj(tm, proj) =>
        Proj(quote(hd, tm, unfold), proj, Irrelevant, Irrelevant)
      case SSplice(tm) => quote(hd, tm, unfold).splice
      case SPrim(sp, x, i, args) =>
        val qhd = (quote(hd, sp, unfold), Expl)
        val qargs = args.map((v, i) => (quote(v, unfold), i))
        val all = qargs.take(i) ++ List(qhd) ++ qargs.drop(i)
        all.foldLeft(Prim(x)) { case (f, (a, i)) =>
          App(f, a, i)
        }
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
      case VRigid(hd, sp)       => quote(quote(hd), sp, unfold)
      case VFlex(id, sp)        => quote(Meta(id), sp, unfold)
      case VGlobal(x, sp, _, _) => quote(Global(x), sp, unfold)
      case VU(s)                => U(quoteS(s))

      case VIntLit(v)    => IntLit(v)
      case VStringLit(v) => StringLit(v)

      case VLam(x, i, ty, b) =>
        Lam(x, i, quote(ty, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VPi(u, x, i, t, b) =>
        Pi(u, x, i, quote(t, unfold), quote(b(VVar(l)), unfold)(l + 1))
      case VFun(u, a, b, c) =>
        Fun(u, quote(a, unfold), quote(b, unfold), quote(c, unfold))
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

      case VForeign(io, rt, cmd, as) =>
        Foreign(
          io,
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

    case PUnitType => (VUMeta(), SMeta)
    case PUnit     => (VUnitType(), SMeta)
    // {R : Meta} (1 _ : ()) (1 _ : R) -> R
    case PConsumeLinearUnit =>
      (vpiI("R", VUMeta(), r => vfun1(VUnitType(), vfun1(r, r))), SMeta)

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
      def vio(a: VTy) = VLift(VComp(), VIO(a))
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
    // unsafePerformIO : {A : VTy} -> ^(IO A) -> ^A
    case PRunIO =>
      (
        vpiI("A", VVTy(), a => vfun(VLift(VComp(), VIO(a)), VLift(VVal(), a))),
        SMeta
      )

    case PArray => (vfun(VVTy(), VVTy()), SMeta)

    case PLabel       => (VUMeta(), SMeta)
    case PEqLabel     => (vfun(VLabel(), vfun(VLabel(), vcbool)), SMeta)
    case PAppendLabel => (vfun(VLabel(), vfun(VLabel(), VLabel())), SMeta)

    // Label -> VTy
    case PForeignType => (vfun(VLabel(), VVTy()), SMeta)

    // VTy -> Label -> VTy
    case PCon => (vfun(VVTy(), vfun(VLabel(), VVTy())), SMeta)
    // {A : VTy} -> {C : Label} -> ^A -> ^(Con A C)
    case PMkCon =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "C",
              VLabel(),
              c => vfun(VLift(VVal(), a), VLift(VVal(), VConType(a, c)))
            )
        ),
        SMeta
      )
    // {A : VTy} -> {C : Label} -> ^(Con A C) -> ^A
    case PConExpose =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "C",
              VLabel(),
              c => vfun(VLift(VVal(), VConType(a, c)), VLift(VVal(), a))
            )
        ),
        SMeta
      )
    // Label -> Label -> Meta
    case PConHasIndex =>
      (vfun(VLabel(), vfun(VLabel(), VUMeta())), SMeta)
    // VTy -> Label -> Label -> VTy
    case PConParamType =>
      (vfun(VVTy(), vfun(VLabel(), vfun(VLabel(), VVTy()))), SMeta)
    // {A : VTy} -> {C : Label} -> ^(Con A C) -> (i : Label) -> ConHasIndex C i -> ^(ConParamType A C i)
    case PConField =>
      (
        vpiI(
          "A",
          VVTy(),
          a =>
            vpiI(
              "C",
              VLabel(),
              c =>
                vfun(
                  VLift(VVal(), VConType(a, c)),
                  vpi(
                    "i",
                    VLabel(),
                    i =>
                      vfun(
                        vprimelim(PConHasIndex, 0, List((i, Expl)), c),
                        VLift(
                          VVal(),
                          vprimelim(
                            PConParamType,
                            0,
                            List((c, Expl), (i, Expl)),
                            a
                          )
                        )
                      )
                  )
                )
            )
        ),
        SMeta
      )

  // (R : Meta) -> R -> R -> R
  val vcbool: Val = vpi("R", VUMeta(), r => vfun(r, vfun(r, r)))

  // (R : Meta) -> R
  val vcvoid: Val = vpi("R", VUMeta(), r => r)
