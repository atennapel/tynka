package core

import common.Common.*
import Syntax as S

import scala.annotation.tailrec

object Value:
  final case class Clos[A](env: Env, tm: A)
  object Clos:
    def apply[A](tm: A)(implicit env: Env): Clos[A] = Clos(env, tm)

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

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case SId             => acc
        case SApp(sp, _, _)  => go(acc + 1, sp)
        case SMetaApp(sp, _) => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case SId             => acc
        case SApp(sp, v, i)  => go(SApp(acc, v, i), sp)
        case SMetaApp(sp, v) => go(SMetaApp(acc, v), sp)
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
        body: Clos[S.Tm0]
    )
    case VLetRec(
        name: Name,
        ty: VTy,
        value: Clos[S.Tm0],
        body: Clos[S.Tm0]
    )
    case VLam0(name: Bind, ty: VTy, body: Clos[S.Tm0])
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

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos[S.Ty])
    case VLam1(name: Bind, icit: Icit, ty: VTy, body: Clos[S.Tm1])

    case VMetaPi(meta: Boolean, ty: VTy, body: Clos[S.Ty])
    case VMetaLam(meta: Boolean, body: Clos[S.Tm1])

    case VU0(cv: VCV)
    case VU1

    case VFun(levity: VTy, pty: VTy, cv: VCV, rty: VTy)
    case VCV1
    case VComp
    case VLift(cv: VCV, ty: VTy)

    case VQuote(tm: Val0)

    case VLabelLit(value: String)
  export Val1.*

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

  object VVal:
    def apply(levity: Val1): Val1 =
      VRigid(HPrim(Name("Val")), SApp(SId, levity, Expl))
    def unapply(value: Val1): Option[Val1] = value match
      case VRigid(HPrim(Name("Val")), SApp(SId, levity, Expl)) => Some(levity)
      case _                                                   => None

  object VUnboxed:
    def apply(rep: Val1): Val1 =
      VRigid(HPrim(Name("Unboxed")), SApp(SId, rep, Expl))
    def unapply(value: Val1): Option[Val1] = value match
      case VRigid(HPrim(Name("Unboxed")), SApp(SId, rep, Expl)) => Some(rep)
      case _                                                    => None

  val VLevity = VPrim1(Name("Levity"))
  val VBoxed = VPrim1(Name("Boxed"))
