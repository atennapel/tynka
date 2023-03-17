package core

import common.Common.*
import Syntax.Tm

object Value:
  type VStage = Stage[Val]
  type Env = List[Val]

  enum Clos:
    case CClos(env: Env, tm: Tm)
    case CFun(fn: Val => Val)
  export Clos.*
  object Clos:
    def apply(tm: Tm)(implicit env: Env): Clos = CClos(env, tm)

  final case class TConClos(env: Env, cs: List[List[Tm]])

  enum Clos2:
    case CClos2(env: Env, tm: Tm)
    case CFun2(fn: (Val, Val) => Val)
  export Clos2.*

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val, icit: Icit)
    case SSplice(spine: Spine)

    def size: Int = this match
      case SId            => 0
      case SApp(sp, _, _) => 1 + sp.size
      case SSplice(sp)    => 1 + sp.size

    def isEmpty: Boolean = this match
      case SId => true
      case _   => false
  export Spine.*

  enum Head:
    case HVar(lvl: Lvl)
  export Head.*

  type VTy = Val
  enum Val:
    case VRigid(head: Head, spine: Spine)
    case VFlex(id: MetaId, spine: Spine)
    case VGlobal(module: String, name: Name, spine: Spine, value: () => Val)
    case VU(stage: VStage)

    case VVF
    case VVal
    case VFun

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos)
    case VTFun(pty: VTy, vf: VTy, rty: VTy)
    case VLam(name: Bind, icit: Icit, fnty: VTy, body: Clos)
    case VFix(ty: VTy, rty: VTy, g: Bind, x: Bind, b: Clos2, arg: Val)

    case VLift(vf: VTy, tm: VTy)
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

  object SVTy:
    def apply(): VStage = STy(VVal)
    def unapply(value: VStage): Boolean = value match
      case STy(VVal) => true
      case _         => false

  object SFTy:
    def apply(): VStage = STy(VFun)
    def unapply(value: VStage): Boolean = value match
      case STy(VFun) => true
      case _         => false

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

  object VUMeta:
    def apply(): Val = VU(SMeta)
    def unapply(value: Val): Boolean = value match
      case VU(SMeta) => true
      case _         => false

  object VUTy:
    def apply(vf: Val): Val = VU(STy(vf))
    def unapply(value: Val): Option[Val] = value match
      case VU(STy(vf)) => Some(vf)
      case _           => None

  object VVTy:
    def apply(): Val = VU(STy(VVal))
    def unapply(value: Val): Boolean = value match
      case VU(STy(VVal)) => true
      case _             => false

  object VFTy:
    def apply(): Val = VU(STy(VFun))
    def unapply(value: Val): Boolean = value match
      case VU(STy(VFun)) => true
      case _             => false
