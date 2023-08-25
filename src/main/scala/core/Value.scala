package core

import common.Common.*
import Syntax.{Tm, ProjType}

object Value:
  type VStage = Stage[Val]
  type Env = List[Val]

  enum Clos:
    case CClos(env: Env, tm: Tm)
    case CFun(fn: Val => Val)
  export Clos.*
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = CClos(env, tm)

  enum Clos2:
    case CClos2(env: Env, tm: Tm)
    case CFun2(fn: (Val, Val) => Val)
  export Clos2.*

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val, icit: Icit)
    case SProj(spine: Spine, proj: ProjType)
    case SSplice(spine: Spine)
    case SPrim(spine: Spine, name: PrimName, ix: Int, args: List[(Val, Icit)])
    case SMatch(
        spine: Spine,
        dty: VTy,
        rty: VTy,
        cs: List[(Name, Boolean, Int, Val)],
        other: Option[Val]
    )

    def size: Int = this match
      case SId                    => 0
      case SApp(sp, _, _)         => 1 + sp.size
      case SProj(sp, _)           => 1 + sp.size
      case SSplice(sp)            => 1 + sp.size
      case SPrim(sp, _, _, _)     => 1 + sp.size
      case SMatch(sp, _, _, _, _) => 1 + sp.size

    def isEmpty: Boolean = this match
      case SId => true
      case _   => false
  export Spine.*

  enum Head:
    case HVar(lvl: Lvl)
    case HPrim(name: PrimName)
  export Head.*

  type VTy = Val
  enum Val:
    case VRigid(head: Head, spine: Spine)
    case VFlex(id: MetaId, spine: Spine)
    case VGlobal(name: Name, spine: Spine, opaque: Boolean, value: () => Val)
    case VU(stage: VStage)

    case VIntLit(value: Int)
    case VStringLit(value: String)

    case VPi(usage: Usage, name: Bind, icit: Icit, ty: VTy, body: Clos)
    case VFun(usage: Usage, pty: VTy, cv: VTy, rty: VTy)
    case VLam(name: Bind, icit: Icit, fnty: VTy, body: Clos)
    case VFix(ty: VTy, rty: VTy, g: Bind, x: Bind, b: Clos2, arg: Val)

    case VSigma(name: Bind, ty: VTy, body: Clos)
    case VPair(fst: Val, snd: Val, ty: VTy)

    case VLift(cv: VTy, tm: VTy)
    case VQuote(tm: Val)

    case VTCon(name: Name, args: List[Val])
    case VCon(name: Name, con: Name, targs: List[Val], args: List[Val])

    case VForeign(io: Boolean, rt: VTy, l: Val, args: List[(Val, VTy)])

    case VIrrelevant
  export Val.*

  private def name(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam(x: String, ty: VTy, f: Val => Val): Val =
    VLam(name(x), Expl, ty, CFun(f))
  def vlamI(x: String, ty: VTy, f: Val => Val): Val =
    VLam(name(x), Impl, ty, CFun(f))
  def vlamIrr(x: String, f: Val => Val): Val =
    VLam(name(x), Expl, VIrrelevant, CFun(f))
  def vlamIrrI(x: String, f: Val => Val): Val =
    VLam(name(x), Impl, VIrrelevant, CFun(f))
  def vpi(x: String, t: Val, f: Val => Val): Val =
    VPi(Many, name(x), Expl, t, CFun(f))
  def vpi1(x: String, t: Val, f: Val => Val): Val =
    VPi(One, name(x), Expl, t, CFun(f))
  def vpiI(x: String, t: Val, f: Val => Val): Val =
    VPi(Many, name(x), Impl, t, CFun(f))
  def vfun(a: Val, b: Val): Val = VPi(Many, DontBind, Expl, a, CFun(_ => b))
  def vfun1(a: Val, b: Val): Val = VPi(One, DontBind, Expl, a, CFun(_ => b))
  def vsigma(x: String, t: Val, f: Val => Val): Val =
    VSigma(name(x), t, CFun(f))

  object SVTy:
    def apply(): VStage = STy(VVal())
    def unapply(value: VStage): Boolean = value match
      case STy(VVal()) => true
      case _           => false

  object SCTy:
    def apply(): VStage = STy(VComp())
    def unapply(value: VStage): Boolean = value match
      case STy(VComp()) => true
      case _            => false

  object VVar:
    def apply(lvl: Lvl): Val = VRigid(HVar(lvl), SId)
    def unapply(value: Val): Option[Lvl] = value match
      case VRigid(HVar(hd), SId) => Some(hd)
      case _                     => None

  object VMeta:
    def apply(id: MetaId): Val = VFlex(id, SId)
    def unapply(value: Val): Option[MetaId] = value match
      case VFlex(id, SId) => Some(id)
      case _              => None

  object VPrim:
    def apply(x: PrimName): Val = VRigid(HPrim(x), SId)
    def unapply(value: Val): Option[PrimName] = value match
      case VRigid(HPrim(x), SId) => Some(x)
      case _                     => None

  object VUMeta:
    def apply(): Val = VU(SMeta)
    def unapply(value: Val): Boolean = value match
      case VU(SMeta) => true
      case _         => false

  object VUTy:
    def apply(cv: Val): Val = VU(STy(cv))
    def unapply(value: Val): Option[Val] = value match
      case VU(STy(cv)) => Some(cv)
      case _           => None

  object VCV:
    def apply(): Val = VRigid(HPrim(PCV), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PCV), SId) => true
      case _                       => false

  object VVal:
    def apply(): Val = VRigid(HPrim(PVal), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PVal), SId) => true
      case _                        => false

  object VComp:
    def apply(): Val = VRigid(HPrim(PComp), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PComp), SId) => true
      case _                         => false

  object VVTy:
    def apply(): Val = VU(STy(VVal()))
    def unapply(value: Val): Boolean = value match
      case VU(STy(VVal())) => true
      case _               => false

  object VCTy:
    def apply(): Val = VU(STy(VComp()))
    def unapply(value: Val): Boolean = value match
      case VU(STy(VComp())) => true
      case _                => false

  object VUnitType:
    def apply(): Val = VRigid(HPrim(PUnitType), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PUnitType), SId) => true
      case _                             => false

  object VUnit:
    def apply(): Val = VRigid(HPrim(PUnit), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PUnit), SId) => true
      case _                         => false

  object VLabel:
    def apply(): Val = VRigid(HPrim(PLabel), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PLabel), SId) => true
      case _                          => false

  object VIO:
    def apply(t: Val): Val = VRigid(HPrim(PIO), SApp(SId, t, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PIO), SApp(SId, t, Expl)) => Some(t)
      case _                                      => None

  object VArray:
    def apply(t: Val): Val = VRigid(HPrim(PArray), SApp(SId, t, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PArray), SApp(SId, t, Expl)) => Some(t)
      case _                                         => None

  object VForeignType:
    def apply(t: Val): Val = VRigid(HPrim(PForeignType), SApp(SId, t, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PForeignType), SApp(SId, t, Expl)) => Some(t)
      case _                                               => None

  object VConType:
    def apply(t: Val, c: Val): Val =
      VRigid(HPrim(PCon), SApp(SApp(SId, t, Expl), c, Expl))
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(HPrim(PCon), SApp(SApp(SId, t, Expl), c, Expl)) =>
        Some((t, c))
      case _ => None

  object VBoolM:
    def apply(): Val = VRigid(HPrim(PBoolM), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PBoolM), SId) => true
      case _                          => false

  object VTrueM:
    def apply(): Val = VRigid(HPrim(PTrueM), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PTrueM), SId) => true
      case _                          => false

  object VFalseM:
    def apply(): Val = VRigid(HPrim(PFalseM), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PFalseM), SId) => true
      case _                           => false

  object VHId:
    def apply(a: Val, b: Val, x: Val, y: Val): Val =
      VRigid(
        HPrim(PHId),
        SApp(SApp(SApp(SApp(SId, a, Impl), b, Impl), x, Expl), y, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val, Val)] = value match
      case VRigid(
            HPrim(PHId),
            SApp(SApp(SApp(SApp(SId, a, Impl), b, Impl), x, Expl), y, Expl)
          ) =>
        Some((a, b, x, y))
      case _ => None

  object VRefl:
    def apply(a: Val, x: Val): Val =
      VRigid(
        HPrim(PRefl),
        SApp(SApp(SId, a, Impl), x, Impl)
      )
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(
            HPrim(PRefl),
            SApp(SApp(SId, a, Impl), x, Impl)
          ) =>
        Some((a, x))
      case _ => None

  object VIFixM:
    def apply(i: Val, f: Val, ii: Val): Val =
      VRigid(
        HPrim(PIFixM),
        SApp(SApp(SApp(SId, i, Impl), f, Expl), ii, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val)] = value match
      case VRigid(
            HPrim(PIFixM),
            SApp(SApp(SApp(SId, i, Impl), f, Expl), ii, Expl)
          ) =>
        Some((i, f, ii))
      case _ => None

  object VIFixM0:
    def apply(i: Val, f: Val): Val =
      VRigid(
        HPrim(PIFixM),
        SApp(SApp(SId, i, Impl), f, Expl)
      )
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(
            HPrim(PIFixM),
            SApp(SApp(SId, i, Impl), f, Expl)
          ) =>
        Some((i, f))
      case _ => None

  object VIIn:
    def apply(i: Val, f: Val, ii: Val, x: Val): Val =
      VRigid(
        HPrim(PIInM),
        SApp(SApp(SApp(SApp(SId, i, Impl), f, Impl), ii, Impl), x, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val, Val)] = value match
      case VRigid(
            HPrim(PIInM),
            SApp(SApp(SApp(SApp(SId, i, Impl), f, Impl), ii, Impl), x, Expl)
          ) =>
        Some((i, f, ii, x))
      case _ => None

  object VRow:
    def apply(): Val = VRigid(HPrim(PRow), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PRow), SId) => true
      case _                        => false

  object VRowEmpty:
    def apply(): Val = VRigid(HPrim(PRowEmpty), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PRowEmpty), SId) => true
      case _                             => false

  object VRowExtend:
    def apply(l: Val, t: Val, r: Val): Val =
      VRigid(
        HPrim(PRowExtend),
        SApp(SApp(SApp(SId, l, Expl), t, Expl), r, Expl)
      )
    def unapply(value: Val): Option[(Val, Val, Val)] = value match
      case VRigid(
            HPrim(PRowExtend),
            SApp(SApp(SApp(SId, l, Expl), t, Expl), r, Expl)
          ) =>
        Some((l, t, r))
      case _ => None

  object VRec:
    def apply(r: Val): Val =
      VRigid(HPrim(PRec), SApp(SId, r, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PRec), SApp(SId, r, Expl)) => Some(r)
      case _                                       => None

  object VVarV:
    def apply(r: Val): Val =
      VRigid(HPrim(PVar), SApp(SId, r, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PVar), SApp(SId, r, Expl)) => Some(r)
      case _                                       => None
