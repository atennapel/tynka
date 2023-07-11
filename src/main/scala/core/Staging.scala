package core

import common.Common.*
import common.Debug.debug
import Syntax.*
import Globals.getGlobal
import ir.Syntax as IR

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.immutable.ListMap

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
    case VPrim1(x: PrimName, args: List[Val1])
    case VLam1(fn: Val1 => Val1)
    case VQuote1(v: Val0)
    case VType1
    case VPair1(fst: Val1, snd: Val1)
    case VTCon1(x: Name, args: List[Val1])
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(x: Name, ty: Val1)
    case VPrim0(x: PrimName)
    case VSplicePrim0(x: PrimName, as: List[Val1])
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VFix0(ty: Val1, rty: Val1, b: (Val0, Val0) => Val0, arg: Val0)
    case VMatch0(
        dty: Val1,
        rty: Val1,
        scrut: Val0,
        cs: List[(Name, Int, Val0)],
        other: Option[Val0]
    )
    case VLet0(ty: Val1, bty: Val1, value: Val0, body: Val0 => Val0)
    case VCon0(x: Name, con: Name, tas: List[Val1], as: List[Val0])
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(e: Env, i: Int): Val1 = (e, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), x) => go(e, x - 1)
      case (Def0(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = (f, a) match
    case (VLam1(f), _)               => f(a)
    case (VPrim1(x, as), _)          => VPrim1(x, as ++ List(a))
    case (VQuote1(f), VQuote1(a))    => VQuote1(VApp0(f, a))
    case (VQuote1(f), VPrim1(p, as)) => VQuote1(VApp0(f, VSplicePrim0(p, as)))
    case _                           => impossible()

  private def vproj1(t: Val1, p: ProjType): Val1 = (t, p) match
    case (VPair1(fst, _), Fst)         => fst
    case (VPair1(_, snd), Snd)         => snd
    case (VPair1(fst, _), Named(_, 0)) => fst
    case (VPair1(_, snd), Named(x, i)) => vproj1(snd, Named(x, i - 1))
    case _                             => impossible()

  private def clos1(t: Tm)(implicit env: Env): Val1 => Val1 =
    v => eval1(t)(Def1(env, v))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Var(x)                => vvar1(x)
    case Global(x)             => eval1(getGlobal(x).get.tm)
    case Prim(x)               => VPrim1(x, Nil)
    case Lam(_, _, _, b)       => VLam1(clos1(b))
    case App(f, a, _)          => vapp1(eval1(f), eval1(a))
    case Proj(t, p, _, _)      => vproj1(eval1(t), p)
    case Let(_, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case Pair(fst, snd, _)     => VPair1(eval1(fst), eval1(snd))
    case Quote(t)              => VQuote1(eval0(t))
    case TCon(x, as)           => VTCon1(x, as.map(eval1))
    case Wk(t)                 => eval1(t)(env.tail)

    case U(_)           => VType1
    case Pi(_, _, _, _) => VType1
    case Sigma(_, _, _) => VType1
    case Lift(_, _)     => VType1
    case Irrelevant     => VType1

    case _ => impossible()

  private def vvar0(ix: Ix)(implicit env: Env): Val0 =
    def go(e: Env, i: Int): Val0 = (e, i) match
      case (Def0(_, v), 0) => v
      case (Def0(e, _), x) => go(e, x - 1)
      case (Def1(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vsplice0(v: Val1): Val0 = v match
    case VQuote1(v)    => v
    case VPrim1(x, as) => VSplicePrim0(x, as)
    case _             => impossible()

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)             => vvar0(x)
    case Global(x)          => VGlobal0(x, eval1(getGlobal(x).get.ty)(Empty))
    case Prim(x)            => VPrim0(x)
    case Lam(x, _, fnty, b) => VLam0(eval1(fnty), clos0(b))
    case Fix(ty, rty, g, x, b, arg) =>
      VFix0(
        eval1(ty),
        eval1(rty),
        (v, w) => eval0(b)(Def0(Def0(env, v), w)),
        eval0(arg)
      )
    case Match(dty, rty, scrut, cs, o) =>
      VMatch0(
        eval1(dty),
        eval1(rty),
        eval0(scrut),
        cs.map((x, i, t) => (x, i, eval0(t))),
        o.map(eval0)
      )
    case App(f, a, _) => VApp0(eval0(f), eval0(a))
    case Let(x, t, _, bt, v, b) =>
      VLet0(eval1(t), eval1(bt), eval0(v), clos0(b))
    case Splice(t)           => vsplice0(eval1(t))
    case Con(x, cx, tas, as) => VCon0(x, cx, tas.map(eval1), as.map(eval0))
    case Wk(t)               => eval0(t)(env.tail)
    case _                   => impossible()

  // quotation
  private type NS = List[(IR.LName, IR.TDef)]
  private type Fresh = () => IR.LName

  private case class DataMonomorphizer(
      typeCache: mutable.Map[Name, DData] = mutable.Map.empty,
      typeOrder: mutable.ArrayBuffer[Name] = mutable.ArrayBuffer.empty,
      cache: mutable.Map[(Name, List[IR.Ty]), IR.GName] = mutable.Map.empty,
      defCache: mutable.ArrayBuffer[IR.DData] = mutable.ArrayBuffer.empty
  ):
    def addDef(ddef: DData): Unit =
      typeCache += ddef.name -> ddef
      typeOrder += ddef.name

    def get(name: Name, cparams: List[Val1]): IR.GName =
      val params = cparams.map(quoteVTy(_)(this))
      cache.get((name, params)) match
        case Some(x) => x
        case None =>
          val x =
            s"${name.expose}${if params.isEmpty then "" else "_"}${params.mkString("_")}"
          cache += (name, params) -> x
          implicit val env: Env = cparams.foldLeft(Empty)(Def1.apply)
          defCache += IR.DData(
            x,
            typeCache(name).cs.map((cx, as) =>
              (cx.expose, as.map(a => quoteVTy(eval1(a))(this)))
            )
          )
          x

    def defs: List[IR.Def] =
      for {
        dx <- typeOrder.toList
        entry <- cache.filter { case ((y, _), _) => dx == y }
        data <- defCache.find(d => d.name == entry._2)
      } yield data

  private def quoteVTy(v: Val1)(implicit dmono: DataMonomorphizer): IR.Ty =
    v match
      case VTCon1(x, as) =>
        val dx = dmono.get(x, as)
        IR.TCon(dx)
      case _ => impossible()

  private def quoteCTy(v: Val1)(implicit dmono: DataMonomorphizer): IR.TDef =
    v match
      case VPrim1(PFun, List(a, _, b)) => IR.TDef(quoteVTy(a), quoteCTy(b))
      case VPrim1(PIO, List(a))        => IR.TDef(Nil, true, quoteVTy(a))
      case _                           => IR.TDef(quoteVTy(v))

  private def quote(
      v: Val0
  )(implicit l: Lvl, ns: NS, fresh: Fresh, dmono: DataMonomorphizer): IR.Tm =
    v match
      case VVar0(lvl) =>
        val (x, t) = ns(lvl.toIx.expose)
        IR.Var(x, t)
      case VGlobal0(x, t) => IR.Global(x.expose, quoteCTy(t))

      case VApp0(f, a) => IR.App(quote(f), quote(a))
      case VLam0(ft, b) =>
        val x = fresh()
        val qt = quoteCTy(ft)
        IR.Lam(
          x,
          qt.head,
          qt.tail,
          quote(b(VVar0(l)))(l + 1, (x, IR.TDef(qt.head)) :: ns, fresh, dmono)
        )
      case VFix0(ty, rty, b, arg) =>
        val ta = quoteVTy(ty)
        val tb = quoteCTy(rty)
        val g = fresh()
        val x = fresh()
        val qf = quote(b(VVar0(l), VVar0(l + 1)))(
          l + 2,
          (x, IR.TDef(ta)) :: (g, IR.TDef(ta, tb)) :: ns,
          fresh,
          dmono
        )
        val qarg = quote(arg)
        IR.Fix(ta, tb, g, x, qf, qarg)

      case VMatch0(dty, rty, scrut, cs, other) =>
        val qdty = quoteVTy(dty)
        val dataname = qdty match
          case IR.TCon(x) => x
        val qdtytd = IR.TDef(quoteVTy(dty))
        val qrty = quoteCTy(rty)
        val x = fresh()
        val vv = IR.Var(x, qdtytd)
        IR.Match(
          dataname,
          qrty,
          x,
          quote(scrut),
          cs.map((cx, i, t) =>
            (
              cx.expose,
              (0 until i).foldLeft(quote(t))((f, i) =>
                IR.App(
                  f,
                  IR.Field(dataname, cx.expose, vv, i)
                )
              )
            )
          ),
          other.map(quote)
        )

      case VLet0(ty, bty, v, b) =>
        val x = fresh()
        val qt = quoteCTy(ty)
        IR.Let(
          x,
          qt,
          quoteCTy(bty),
          quote(v),
          quote(b(VVar0(l)))(l + 1, (x, qt) :: ns, fresh, dmono)
        )

      case VCon0(x, cx, tas, as) =>
        val dx = dmono.get(x, tas)
        IR.Con(dx, cx.expose, as.map(quote))

      case VSplicePrim0(PReturnIO, List(ty, v)) =>
        IR.ReturnIO(quote(vsplice0(v)))
      case VSplicePrim0(PBindIO, List(t1, t2, c, k)) =>
        val x = fresh()
        val qt1 = quoteVTy(t1)
        val qt2 = quoteVTy(t2)
        val qk = quote(vsplice0(vapp1(k, VQuote1(VVar0(l)))))(
          l + 1,
          (x, IR.TDef(qt1)) :: ns,
          fresh,
          dmono
        )
        IR.BindIO(qt1, qt2, x, quote(vsplice0(c)), qk)

      case VPrim0(_)           => impossible()
      case VSplicePrim0(x, as) => impossible()

  // staging
  private def stageCTy(t: Ty)(implicit dmono: DataMonomorphizer): IR.TDef =
    quoteCTy(eval1(t)(Empty))

  private def stageTm(
      tm: Tm
  )(implicit fresh: Fresh, dmono: DataMonomorphizer): IR.Tm =
    quote(eval0(tm)(Empty))(lvl0, Nil, fresh, dmono)

  private def newFresh(): Fresh =
    var n = 0
    () => {
      val c = n
      n += 1
      c
    }

  private def stageDef(d: Def)(implicit
      dmono: DataMonomorphizer
  ): Option[IR.Def] = d match
    case DDef(x, t, st @ STy(_), v) =>
      implicit val fresh: Fresh = newFresh()
      val ty = stageCTy(t)
      val value = stageTm(v)
      Some(IR.DDef(x.expose, false, ty, value))
    case d @ DData(_, _, _) => dmono.addDef(d); None
    case _                  => None

  def stage(ds: Defs): IR.Defs =
    implicit val dmono: DataMonomorphizer = DataMonomorphizer()
    val sds = ds.toList.flatMap(d => stageDef(d))
    IR.Defs(dmono.defs ++ sds)
