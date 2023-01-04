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

    def size: Int = this match
      case SId            => 0
      case SApp(sp, _, _) => 1 + sp.size
      case SProj(sp, _)   => 1 + sp.size
  export Spine.*

  enum Head:
    case HVar(lvl: Lvl)
  export Head.*

  type VTy = Val
  enum Val:
    case VRigid(head: Head, spine: Spine)
    case VFlex(id: MetaId, spine: Spine)
    case VGlobal(name: Name, spine: Spine, value: () => Val)
    case VType

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos)
    case VLam(name: Bind, icit: Icit, body: Clos)

    case VSigma(name: Bind, ty: VTy, body: Clos)
    case VPair(fst: Val, snd: Val)
  export Val.*

  private def name(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam(x: String, f: Val => Val): Val = VLam(name(x), Expl, CFun(f))
  def vpi(x: String, t: Val, f: Val => Val): Val =
    VPi(name(x), Expl, t, CFun(f))

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
