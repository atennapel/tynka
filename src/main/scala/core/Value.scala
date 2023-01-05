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

  enum Spine:
    case SId
    case SApp(spine: Spine, arg: Val, icit: Icit)
    case SProj(spine: Spine, proj: ProjType)
    case SPrim(spine: Spine, name: PrimName, args: List[(Val, Icit)])

    def size: Int = this match
      case SId             => 0
      case SApp(sp, _, _)  => 1 + sp.size
      case SProj(sp, _)    => 1 + sp.size
      case SPrim(sp, _, _) => 1 + sp.size
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

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos)
    case VLam(name: Bind, icit: Icit, body: Clos)

    case VSigma(name: Bind, ty: VTy, body: Clos)
    case VPair(fst: Val, snd: Val)
  export Val.*

  private def name(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam(x: String, f: Val => Val): Val = VLam(name(x), Expl, CFun(f))
  def vlamI(x: String, f: Val => Val): Val = VLam(name(x), Impl, CFun(f))
  def vpi(x: String, t: Val, f: Val => Val): Val =
    VPi(name(x), Expl, t, CFun(f))
  def vpiI(x: String, t: Val, f: Val => Val): Val =
    VPi(name(x), Impl, t, CFun(f))
  def vfun(a: Val, b: Val): Val = VPi(DontBind, Expl, a, CFun(_ => b))

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

  object VType:
    def apply(): Val = VRigid(HPrim(PType), SId)
    def unapply(value: Val): Boolean = value match
      case VRigid(HPrim(PType), SId) => true
      case _                         => false

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
