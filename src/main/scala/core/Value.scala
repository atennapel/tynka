package core

import common.Common.*
import Syntax as S

import scala.annotation.tailrec

object Value:
  enum Clos0:
    case CClos0(env: Env, tm: S.Tm0)
    case CFun0(fn: Val0 => Val0)
  export Clos0.*
  object Clos0:
    def apply(tm: S.Tm0)(implicit env: Env): Clos0 = CClos0(env, tm)

  enum Clos1:
    case CClos1(env: Env, tm: S.Tm1)
    case CFun1(fn: Val1 => Val1)
  export Clos1.*
  object Clos1:
    def apply(tm: S.Tm1)(implicit env: Env): Clos1 = CClos1(env, tm)

  enum Env:
    case EEmpty
    case E1(env: Env, value: Val1)
    case E0(env: Env, value: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, e: Env): Int = e match
        case EEmpty   => acc
        case E1(e, _) => go(acc + 1, e)
        case E0(e, _) => go(acc + 1, e)
      go(0, this)

    inline def wk1: Env = this match
      case E1(env, _) => env
      case _          => impossible()

    inline def wk0: Env = this match
      case E0(env, _) => env
      case _          => impossible()

    inline def tail: Env = this match
      case E0(env, _) => env
      case E1(env, _) => env
      case _          => impossible()
  export Env.*
  object Env:
    def apply(vs: List[Val1]): Env = vs.foldLeft(EEmpty)(E1.apply)

  type VTy = Val1
  type VCV = VTy

  enum Spine:
    case SId
    case SApp(sp: Spine, arg: Val1, icit: Icit)
    case SMetaApp(sp: Spine, arg: Either[Val0, Val1])
    case SPrim(
        sp: Spine,
        ix: Int,
        i: Icit,
        name: Name,
        args: List[(Val1, Icit)]
    )

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case SId                   => acc
        case SApp(sp, _, _)        => go(acc + 1, sp)
        case SMetaApp(sp, _)       => go(acc + 1, sp)
        case SPrim(sp, _, _, _, _) => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case SId                     => acc
        case SApp(sp, v, i)          => go(SApp(acc, v, i), sp)
        case SMetaApp(sp, v)         => go(SMetaApp(acc, v), sp)
        case SPrim(sp, ix, i, x, as) => go(SPrim(acc, ix, i, x, as), sp)
      go(SId, this)
  export Spine.*

  enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(name: Name)
    case VPrim0(name: Name)
    case VIntLit(value: Int)
    case VStringLit(value: String)
    case VLet0(
        name: Name,
        ty: VTy,
        value: Val0,
        body: Clos0
    )
    case VLetRec(
        name: Name,
        ty: VTy,
        value: Clos0,
        body: Clos0
    )
    case VLam0(name: Bind, ty: VTy, body: Clos0)
    case VApp0(fn: Val0, arg: Val0)
    case VCon(name: Name, ty: VTy, args: List[Val0])
    case VMatch(
        scrut: Val0,
        ty: VTy,
        con: Name,
        params: List[VTy],
        body: Val0,
        other: Val0
    )
    case VImpossible(ty: VTy)
    case VSplice(tm: Val1)
    case VForeign(io: Boolean, ty: VTy, code: Val1, args: List[Val0])
  export Val0.*

  enum Head:
    case HVar(lvl: Lvl)
    case HPrim(name: Name)
    case HTCon(name: Name)
  export Head.*

  enum UHead:
    case UMeta(id: MetaId)
    case UGlobal(name: Name)
  export UHead.*

  enum Val1:
    case VRigid(head: Head, spine: Spine)
    case VFlex(id: MetaId, spine: Spine)
    case VUnfold(head: UHead, spine: Spine, value: () => Val1)

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos1)
    case VLam1(name: Bind, icit: Icit, ty: VTy, body: Clos1)

    case VMetaPi(meta: Boolean, ty: VTy, body: Clos1)
    case VMetaLam(meta: Boolean, body: Clos1)

    case VU0(cv: VCV)
    case VU1

    case VFun(boxity: VTy, pty: VTy, cv: VCV, rty: VTy)
    case VLift(cv: VCV, ty: VTy)

    case VQuote(tm: Val0)

    case VLabelLit(value: String)
  export Val1.*

  private inline def bind(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam1(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VLam1(bind(x), Expl, ty, CFun1(b))
  def vfun1(ty: VTy, rt: VTy): Val1 = VPi(DontBind, Expl, ty, CFun1(_ => rt))
  def vpi(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VPi(bind(x), Expl, ty, CFun1(b))
  def vpiI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VPi(bind(x), Impl, ty, CFun1(b))

  object VVar1:
    def apply(lvl: Lvl): Val1 = VRigid(HVar(lvl), SId)
    def unapply(value: Val1): Option[Lvl] = value match
      case VRigid(HVar(hd), SId) => Some(hd)
      case _                     => None

  object VPrim1:
    def apply(name: Name): Val1 = VRigid(HPrim(name), SId)
    def unapply(value: Val1): Option[Name] = value match
      case VRigid(HPrim(name), SId) => Some(name)
      case _                        => None

  object VTCon:
    def apply(name: Name): Val1 = VRigid(HTCon(name), SId)
    def unapply(value: Val1): Option[Name] = value match
      case VRigid(HTCon(name), SId) => Some(name)
      case _                        => None

  object VTConApp:
    def apply(name: Name, sp: List[(VTy, Icit)]): Val1 = VRigid(
      HTCon(name),
      sp.foldLeft(SId) { case (sp, (t, i)) => SApp(sp, t, i) }
    )
    def unapply(value: Val1): Option[(Name, List[(VTy, Icit)])] = value match
      case VRigid(HTCon(name), sp) =>
        def go(sp: Spine): List[(VTy, Icit)] = sp match
          case SId            => Nil
          case SApp(sp, t, i) => (t, i) :: go(sp)
          case _              => impossible()
        Some((name, go(sp).reverse))
      case _ => None
