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
        cs: List[(Name, Int, Val)],
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
