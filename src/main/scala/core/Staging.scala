package core

import common.Common.*
import common.Debug.debug
import common.Ref
import Syntax.*
import Globals.getGlobal
import ho.Syntax as HO

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer

object Staging:
  // evaluation
  private enum Env:
    case Empty
    case Def0(e: Env, v: Val0)
    case Def1(e: Env, v: Val1)

    def tail: Env = this match
      case Def0(e, _) => e
      case Def1(e, _) => e
      case _          => impossible()
  import Env.*

  private enum Val1:
    case VLam1(fn: Val1 => Val1)
    case VQuote1(v: Val0)
    case VTFun1(pty: Val1, rty: Val1)
    case VType1
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(m: String, x: Name, ty: Val1)
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VFix0(ty: Val1, rty: Val1, b: (Val0, Val0) => Val0, arg: Val0)
    case VLet0(ty: Val1, bty: Val1, value: Val0, body: Val0 => Val0)
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(e: Env, i: Int): Val1 = (e, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), x) => go(e, x - 1)
      case (Def0(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = (f, a) match
    case (VLam1(f), _)            => f(a)
    case (VQuote1(f), VQuote1(a)) => VQuote1(VApp0(f, a))
    case _                        => impossible()

  private def clos1(t: Tm)(implicit env: Env): Val1 => Val1 =
    v => eval1(t)(Def1(env, v))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Var(x)                => vvar1(x)
    case Global(m, x)          => eval1(getGlobal(m, x).get.tm)
    case Lam(_, _, _, b)       => VLam1(clos1(b))
    case App(f, a, _)          => vapp1(eval1(f), eval1(a))
    case Let(_, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case Quote(t)              => VQuote1(eval0(t))
    case Wk(t)                 => eval1(t)(env.tail)
    case TFun(a, _, b)         => VTFun1(eval1(a), eval1(b))
    case U(_)                  => VType1
    case Pi(_, _, _, _)        => VType1
    case Lift(_, _)            => VType1
    case Irrelevant            => VType1
    case _                     => impossible()

  private def vvar0(ix: Ix)(implicit env: Env): Val0 =
    def go(e: Env, i: Int): Val0 = (e, i) match
      case (Def0(_, v), 0) => v
      case (Def0(e, _), x) => go(e, x - 1)
      case (Def1(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vsplice0(v: Val1): Val0 = v match
    case VQuote1(v) => v
    case _          => impossible()

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)       => vvar0(x)
    case Global(m, x) => VGlobal0(m, x, eval1(getGlobal(m, x).get.ty)(Empty))
    case Lam(x, _, fnty, b) => VLam0(eval1(fnty), clos0(b))
    case Fix(ty, rty, g, x, b, arg) =>
      VFix0(
        eval1(ty),
        eval1(rty),
        (v, w) => eval0(b)(Def0(Def0(env, v), w)),
        eval0(arg)
      )
    case App(f, a, _) => VApp0(eval0(f), eval0(a))
    case Let(x, t, _, bt, v, b) =>
      VLet0(eval1(t), eval1(bt), eval0(v), clos0(b))
    case Splice(t) => vsplice0(eval1(t))
    case Wk(t)     => eval0(t)(env.tail)
    case _         => impossible()

  // quotation
  private type NS = List[(HO.LName, HO.TDef)]
  private type Fresh = () => HO.LName

  private def quoteVTy(v: Val1): HO.Ty = v match
    case _ => impossible()

  private def quoteFTy(v: Val1): HO.TDef = v match
    case VTFun1(a, b) => HO.TDef(quoteVTy(a), quoteFTy(b))
    case _            => HO.TDef(quoteVTy(v))

  private def quote(v: Val0)(implicit l: Lvl, ns: NS, fresh: Fresh): HO.Tm =
    v match
      case VVar0(lvl) =>
        val (x, t) = ns(lvl.toIx.expose)
        HO.Var(x, t)
      case VGlobal0(m, x, t) => HO.Global(m, x.expose, quoteFTy(t))

      case VApp0(f, a) => HO.App(quote(f), quote(a))
      case VLam0(ft, b) =>
        val x = fresh()
        val qt = quoteFTy(ft)
        HO.Lam(
          x,
          qt.head,
          qt.tail,
          quote(b(VVar0(l)))(l + 1, (x, HO.TDef(qt.head)) :: ns, fresh)
        )
      case VFix0(ty, rty, b, arg) =>
        val ta = quoteVTy(ty)
        val tb = quoteFTy(rty)
        val g = fresh()
        val x = fresh()
        val qf = quote(b(VVar0(l), VVar0(l + 1)))(
          l + 2,
          (x, HO.TDef(ta)) :: (g, HO.TDef(ta, tb)) :: ns,
          fresh
        )
        val qarg = quote(arg)
        HO.Fix(ta, tb, g, x, qf, qarg)
      case VLet0(ty, bty, v, b) =>
        val x = fresh()
        val qt = quoteFTy(ty)
        HO.Let(
          x,
          false,
          qt,
          quoteFTy(bty),
          quote(v),
          quote(b(VVar0(l)))(l + 1, (x, qt) :: ns, fresh)
        )

  // staging
  private def stageFTy(t: Ty): HO.TDef = quoteFTy(eval1(t)(Empty))

  private def stageTm(tm: Tm)(implicit fresh: Fresh): HO.Tm =
    quote(eval0(tm)(Empty))(lvl0, Nil, fresh)

  private def newFresh(): Fresh =
    var n = 0
    () => {
      val c = n
      n += 1
      c
    }

  private def stageDef(module: String, d: Def): Option[HO.Def] = d match
    case DDef(m, x, t, st @ STy(_), v) =>
      implicit val fresh: Fresh = newFresh()
      val ty = stageFTy(t)
      val value = stageTm(v)
      Some(HO.DDef(m, x.expose, false, ty, value))
    case _ => None

  def stage(module: String, ds: Defs): HO.Defs =
    val sds = ds.toList.flatMap(d => stageDef(module, d))
    HO.Defs(sds)
