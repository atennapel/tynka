package core

import common.Common.*
import common.Debug.debug
import Syntax.*
import Globals.getGlobal
import ir.Syntax as IR

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.immutable.ListMap
import jvmir.JvmName.escape

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
    case VVar1(lvl: Lvl)
    case VPrim1(x: PrimName, args: List[Val1])
    case VFun1(t1: Val1, t2: Val1)
    case VLam1(fn: Val1 => Val1)
    case VQuote1(v: Val0)
    case VType1
    case VPair1(fst: Val1, snd: Val1)
    case VData1(
        x: Bind,
        cs: List[(Name, List[(Bind, Tm)])],
        env: Env,
        cache: Option[String]
    )
    case VStringLit1(v: String)
  import Val1.*

  private var gensymId = 0
  private def gensymStr(): String =
    val v = s"$$$gensymId"
    gensymId += 1
    v
  private def gensym(): Val1 = VStringLit1(gensymStr())

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(m: String, x: Name, ty: Val1)
    case VPrim0(x: PrimName)
    case VSplicePrim0(x: PrimName, as: List[Val1])
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VFix0(ty: Val1, rty: Val1, b: (Val0, Val0) => Val0, arg: Val0)
    case VMatch0(
        dty: Val1,
        rty: Val1,
        scrut: Val0,
        cs: List[(Name, Boolean, Int, Val0)],
        other: Option[Val0]
    )
    case VLet0(ty: Val1, bty: Val1, value: Val0, body: Val0 => Val0)
    case VCon0(c: Name, t: Val1, as: List[Val0])
    case VStringLit0(v: String)
    case VIntLit0(v: Int)
    case VForeign0(io: Boolean, ty: Val1, cmd: String, as: List[(Val0, Val1)])
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(e: Env, i: Int): Val1 = (e, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), x) => go(e, x - 1)
      case (Def0(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = (f, a) match
    case (VLam1(f), _) => f(a)
    case (VPrim1(x, as), _) =>
      (x, as ++ List(a)) match
        case (PEqLabel, List(VStringLit1(a), VStringLit1(b))) =>
          if a == b then VLam1(r => VLam1(a => VLam1(b => a)))
          else VLam1(r => VLam1(a => VLam1(b => b)))
        case (PAppendLabel, List(VStringLit1(a), VStringLit1(b))) =>
          VStringLit1(a + b)
        case (PConsumeLinearUnit, List(_, _, v))               => v
        case (PUnsafeLinearFunction, List(_, _, f))            => f
        case (PElimBoolM, List(_, t, _, VPrim1(PTrueM, Nil)))  => t
        case (PElimBoolM, List(_, _, f, VPrim1(PFalseM, Nil))) => f
        case (PElimHId, List(_, _, _, refl, _, VPrim1(PRefl, List(_, _)))) =>
          refl
        // elimIFix {I} {F} P alg {i} (IIn {I} {F} {i} x) ~> alg (\{j} y. elimIFix {I} {F} p alg {j} y) {i} x
        case (
              PElimIFixM,
              List(i, f, p, alg, ii, VPrim1(PIInM, List(_, _, _, x)))
            ) =>
          vapp1(
            vapp1(
              vapp1(
                alg,
                VLam1(j =>
                  VLam1(y =>
                    vapp1(VPrim1(PElimIFixM, List(i, f, p, alg, j)), y)
                  )
                )
              ),
              ii
            ),
            x
          )
        case _ => VPrim1(x, as ++ List(a))
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

  private def eval1(t: Tm)(implicit env: Env): Val1 =
    t match
      case Var(x)                   => vvar1(x)
      case Global(m, x)             => eval1(getGlobal(m, x).get.tm)
      case Prim(x)                  => VPrim1(x, Nil)
      case Lam(_, _, _, b)          => VLam1(clos1(b))
      case App(f, a, _)             => vapp1(eval1(f), eval1(a))
      case Proj(t, p, _, _)         => vproj1(eval1(t), p)
      case Let(_, _, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
      case Pair(fst, snd, _)        => VPair1(eval1(fst), eval1(snd))
      case Quote(t)                 => VQuote1(eval0(t))
      case Data(x, cs)              => VData1(x, cs, env, None)
      case Wk(t)                    => eval1(t)(env.tail)
      case StringLit(v)             => VStringLit1(v)
      case Fun(_, t1, _, t2)        => VFun1(eval1(t1), eval1(t2))

      case U(_)              => VType1
      case Pi(_, _, _, _, _) => VType1
      case Sigma(_, _, _)    => VType1
      case Lift(_, _)        => VType1
      case Irrelevant        => VType1

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

  private def eval0(t: Tm)(implicit env: Env): Val0 =
    t match
      case Var(x)       => vvar0(x)
      case Global(m, x) => VGlobal0(m, x, eval1(getGlobal(m, x).get.ty)(Empty))
      case Prim(x)      => VPrim0(x)
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
          cs.map((x, c, i, t) => (x, c, i, eval0(t))),
          o.map(eval0)
        )
      case App(f, a, _) => VApp0(eval0(f), eval0(a))
      case Let(_, x, t, _, bt, v, b) =>
        VLet0(eval1(t), eval1(bt), eval0(v), clos0(b))
      case Splice(t)     => vsplice0(eval1(t))
      case Con(x, t, as) => VCon0(x, eval1(t), as.map(eval0))
      case Wk(t)         => eval0(t)(env.tail)
      case StringLit(v)  => VStringLit0(v)
      case IntLit(v)     => VIntLit0(v)
      case Foreign(io, rt, cmd, as) =>
        val l = eval1(cmd) match
          case VStringLit1(v) => v
          case _              => impossible()
        VForeign0(io, eval1(rt), l, as.map((a, t) => (eval0(a), eval1(t))))
      case _ => impossible()

  // quotation
  private type NS = List[(IR.LName, IR.TDef)]
  private type Fresh = () => IR.LName

  private val primitives = "BCDFIJSZ".split("")
  private def descriptorIsPrimitive(d: String): Boolean = primitives.contains(d)

  private def conv(a: Val1, b: Val1)(implicit l: Lvl): Boolean =
    if a == b then true
    else
      (a, b) match
        case (VVar1(la), VVar1(lb)) => la == lb
        case (VData1(x, cs1, e1, Some(sx)), VData1(y, cs2, e2, Some(sy)))
            if sx == sy =>
          true
        case (VData1(x, cs1, e1, _), VData1(y, cs2, e2, _))
            if cs1.size == cs2.size =>
          cs1
            .sortBy((x, _) => x.expose)
            .zip(cs2.sortBy((x, _) => x.expose))
            .forall {
              case ((cx1, as1), (cx2, as2))
                  if cx1 == cx2 && as1.size == as2.size =>
                as1.zip(as2).forall { case ((_, t1), (_, t2)) =>
                  conv(
                    eval1(t1)(Def1(e1, VVar1(l))),
                    eval1(t2)(Def1(e2, VVar1(l)))
                  )(
                    l + 1
                  )
                }
              case _ => false
            }
        case (VPrim1(x, as1), VPrim1(y, as2))
            if x == y && as1.size == as2.size =>
          as1.zip(as2).forall(conv)
        case (VPair1(a1, b1), VPair1(a2, b2)) => conv(a1, a2) && conv(b1, b2)
        case (VStringLit1(a), VStringLit1(b)) => a == b
        case _                                => false

  private case class DataMonomorphizer(
      module: String,
      cache: mutable.ArrayBuffer[(VData1, IR.GName)] =
        mutable.ArrayBuffer.empty,
      defsCache: mutable.ArrayBuffer[IR.Def] = mutable.ArrayBuffer.empty
  ):
    def get(d: VData1): IR.GName =
      d.cache match
        case Some(x) => x
        case None =>
          cache
            .find((d2, _) => d == d2 || conv(d, d2)(lvl0))
            .map((_, x) => x) match
            case Some(x) => x
            case None =>
              val x = s"D${gensymStr()}"
              cache += (d -> x)
              defsCache += IR.DData(
                x,
                d.cs.map((cx, as) =>
                  (
                    cx.expose,
                    as.map((_, t) =>
                      quoteVTy(
                        eval1(t)(Def1(d.env, VData1(d.x, d.cs, d.env, Some(x))))
                      )(this)
                    )
                  )
                )
              )
              x

    def defs: List[IR.Def] = defsCache.toList

  private def quoteVTy(v: Val1)(implicit dmono: DataMonomorphizer): IR.Ty =
    v match
      case VData1(_, cs, e, Some(x))  => IR.TCon(x)
      case d @ VData1(x, cs, e, None) => IR.TCon(dmono.get(d))
      case VPrim1(PCon, List(t, VStringLit1(c))) =>
        quoteVTy(t) match
          case IR.TCon(dx) => IR.TConCon(dx, c)
          case _           => impossible()
      case VPrim1(PForeignType, List(VStringLit1(d))) => IR.TForeign(d)
      case VPrim1(PArray, List(t))                    => IR.TArray(quoteVTy(t))
      case _                                          => impossible()

  private def quoteCTy(v: Val1)(implicit dmono: DataMonomorphizer): IR.TDef =
    v match
      case VFun1(a, b)          => IR.TDef(quoteVTy(a), quoteCTy(b))
      case VPrim1(PIO, List(a)) => IR.TDef(Nil, true, quoteVTy(a))
      case _                    => IR.TDef(quoteVTy(v))

  private def quote(
      v: Val0
  )(implicit l: Lvl, ns: NS, fresh: Fresh, dmono: DataMonomorphizer): IR.Tm =
    v match
      case VVar0(lvl) =>
        val (x, t) = ns(lvl.toIx.expose)
        IR.Var(x, t)
      case VGlobal0(m, x, t) =>
        IR.Global(m, x.expose, quoteCTy(t))

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
          case _          => impossible()
        val qdtytd = IR.TDef(quoteVTy(dty))
        val qrty = quoteCTy(rty)
        val x = fresh()
        val vv = IR.Var(x, qdtytd)
        IR.Match(
          dataname,
          qrty,
          x,
          quote(scrut),
          cs.map((cx, includeCon, i, t) =>
            val qt0 = quote(t)
            val qt = if includeCon then IR.App(qt0, vv) else qt0
            val qb = (0 until i).foldLeft(qt)((f, i) =>
              IR.App(
                f,
                IR.Field(dataname, cx.expose, vv, i)
              )
            )
            (cx.expose, qb)
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

      case VCon0(x, d @ VData1(_, _, _, _), as) =>
        val dx = dmono.get(d)
        IR.Con(dx, x.expose, as.map(quote))
      case VCon0(_, _, _) => impossible()

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
      case VSplicePrim0(PRunIO, List(_, c)) => IR.RunIO(quote(vsplice0(c)))

      case VIntLit0(v)    => IR.IntLit(v)
      case VStringLit0(v) => IR.StringLit(v)

      case VForeign0(io, ty, cmd, as) =>
        IR.Foreign(
          io,
          quoteVTy(ty),
          cmd,
          as.map((a, t) => (quote(a), quoteVTy(t)))
        )

      case VSplicePrim0(PConExpose, List(_, _, v)) => quote(vsplice0(v))

      case VPrim0(x)           => impossible()
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
    case DDef(m, x, t, st @ STy(_), v) =>
      implicit val fresh: Fresh = newFresh()
      val ty = stageCTy(t)
      val value = stageTm(v)
      Some(IR.DDef(m, x.expose, false, ty, value))
    case _ => None

  def stage(module: String, ds: Defs): IR.Defs =
    implicit val dmono: DataMonomorphizer = DataMonomorphizer(module)
    val sds = ds.toList.flatMap(d => stageDef(d))
    IR.Defs(dmono.defs ++ sds)
