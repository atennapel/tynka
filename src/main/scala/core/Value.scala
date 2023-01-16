package core

import common.Common.*
import Syntax.{Tm, ProjType}
object Value:
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
    case SPrim(spine: Spine, name: PrimName, args: List[(Val, Icit)])

    def size: Int = this match
      case SId             => 0
      case SApp(sp, _, _)  => 1 + sp.size
      case SProj(sp, _)    => 1 + sp.size
      case SSplice(sp)     => 1 + sp.size
      case SPrim(sp, _, _) => 1 + sp.size

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
    case VGlobal(name: Name, spine: Spine, value: () => Val)
    case VU(stage: Stage)

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos)
    case VLam(name: Bind, icit: Icit, fnty: VTy, body: Clos)
    case VFix(go: Name, name: Name, fnty: VTy, body: Clos2, arg: Val)

    case VSigma(name: Bind, ty: VTy, body: Clos)
    case VPair(fst: Val, snd: Val, ty: VTy)

    case VIntLit(value: Int)

    case VLift(tm: Val)
    case VQuote(tm: Val)

    case VIrrelevant
  export Val.*

  private def name(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam(x: String, ty: VTy, f: Val => Val): Val =
    VLam(name(x), Expl, ty, CFun(f))
  def vlamI(x: String, ty: VTy, f: Val => Val): Val =
    VLam(name(x), Impl, ty, CFun(f))
  def vpi(x: String, t: Val, f: Val => Val): Val =
    VPi(name(x), Expl, t, CFun(f))
  def vpiI(x: String, t: Val, f: Val => Val): Val =
    VPi(name(x), Impl, t, CFun(f))
  def vfun(a: Val, b: Val): Val = VPi(DontBind, Expl, a, CFun(_ => b))
  def vsigma(x: String, t: Val, f: Val => Val): Val =
    VSigma(name(x), t, CFun(f))

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

  object VMetaTy:
    def apply(): Val = VU(SMeta)
    def unapply(value: Val): Boolean = value match
      case VU(SMeta) => true
      case _         => false

  object VTy:
    def apply(): Val = VU(STy)
    def unapply(value: Val): Boolean = value match
      case VU(STy) => true
      case _       => false

  object VValTy:
    def apply(): Val = VU(SValTy)
    def unapply(value: Val): Boolean = value match
      case VU(SValTy) => true
      case _          => false

  object VVal:
    def apply(v: Val): Val = VRigid(HPrim(PVal), SApp(SId, v, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PVal), SApp(SId, v, Expl)) => Some(v)
      case _                                       => None

  object VFun:
    def apply(a: Val, b: Val): Val =
      VRigid(HPrim(PFun), SApp(SApp(SId, a, Expl), b, Expl))
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(HPrim(PFun), SApp(SApp(SId, a, Expl), b, Expl)) =>
        Some((a, b))
      case _ => None

  object VPairTy:
    def apply(a: Val, b: Val): Val =
      VRigid(HPrim(PPair), SApp(SApp(SId, a, Expl), b, Expl))
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(HPrim(PPair), SApp(SApp(SId, a, Expl), b, Expl)) =>
        Some((a, b))
      case _ => None

  object VVoid:
    def apply(): Val = VRigid(HPrim(PVoid), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PVoid), SId) => true
      case _                         => false

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

  object VBool:
    def apply(): Val = VRigid(HPrim(PBool), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PBool), SId) => true
      case _                         => false

  object VTrue:
    def apply(): Val = VRigid(HPrim(PTrue), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PTrue), SId) => true
      case _                         => false

  object VFalse:
    def apply(): Val = VRigid(HPrim(PFalse), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PFalse), SId) => true
      case _                          => false

  object VInt:
    def apply(): Val = VRigid(HPrim(PInt), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PInt), SId) => true
      case _                        => false

  object VList:
    def apply(t: Val): Val = VRigid(HPrim(PList), SApp(SId, t, Expl))
    def unapply(value: Val): Option[Val] = value match
      case VRigid(HPrim(PList), SApp(SId, t, Expl)) => Some(t)
      case _                                        => None

  object VEither:
    def apply(a: Val, b: Val): Val =
      VRigid(HPrim(PEither), SApp(SApp(SId, a, Expl), b, Expl))
    def unapply(value: Val): Option[(Val, Val)] = value match
      case VRigid(HPrim(PEither), SApp(SApp(SId, a, Expl), b, Expl)) =>
        Some((a, b))
      case _ => None
