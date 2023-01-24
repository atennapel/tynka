package core

import common.Common.*
import Syntax.*
import Globals.getGlobal
import ir.Syntax as IR

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer

object Staging:
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
    case VFunTy1(pt: Val1, rt: Val1)
    case VPairTy1(pt: Val1, rt: Val1)
    case VPair1(fst: Val1, snd: Val1)
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(x: Name, ty: Val1)
    case VPrim0(x: PrimName)
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VFix0(
        fnty: Val1,
        body: (Val0, Val0) => Val0,
        arg: Val0
    )
    case VLet0(ty: Val1, value: Val0, body: Val0 => Val0)
    case VPair0(fst: Val0, snd: Val0, ty: Val1)
    case VFst0(ty: Val1, t: Val0)
    case VSnd0(ty: Val1, t: Val0)
    case VIntLit0(n: Int)
    case VSplicePrim0(x: PrimName, as: List[Val1])
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(e: Env, i: Int): Val1 = (e, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), x) => go(e, x - 1)
      case (Def0(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = f match
    case VLam1(f)      => f(a)
    case VPrim1(x, as) => VPrim1(x, as ++ List(a))
    case _             => impossible()

  private def vproj1(t: Val1, p: ProjType): Val1 = (t, p) match
    case (VPair1(fst, _), Fst)         => fst
    case (VPair1(_, snd), Snd)         => snd
    case (VPair1(fst, _), Named(_, 0)) => fst
    case (VPair1(_, snd), Named(x, i)) => vproj1(snd, Named(x, i - 1))
    case _                             => impossible()

  private def velimty1(p: Val1, v: Val1, f: Val1, t: Val1): Val1 = t match
    case VPrim1(PVal, List(a)) => vapp1(v, a)
    case VPrim1(PFun, List(a, b)) =>
      vapp1(vapp1(vapp1(f, a), b), velimty1(p, v, f, b))
    case _ => impossible()

  private def vprim1(x: PrimName): Val1 = x match
    case PElimTy =>
      VLam1(p => VLam1(v => VLam1(f => VLam1(t => velimty1(p, v, f, t)))))
    case _ => VPrim1(x, Nil)

  private def clos1(t: Tm)(implicit env: Env): Val1 => Val1 =
    v => eval1(t)(Def1(env, v))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Var(x)                => vvar1(x)
    case Global(x)             => eval1(getGlobal(x).get.tm)
    case Prim(x)               => vprim1(x)
    case Lam(_, _, _, b)       => VLam1(clos1(b))
    case App(f, a, _)          => vapp1(eval1(f), eval1(a))
    case Proj(t, p, _)         => vproj1(eval1(t), p)
    case Let(_, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case Pair(fst, snd, _)     => VPair1(eval1(fst), eval1(snd))
    case Quote(t)              => VQuote1(eval0(t))
    case Wk(t)                 => eval1(t)(env.tail)

    case U(_)           => VType1
    case Pi(_, _, _, _) => VType1
    case Sigma(_, _, _) => VType1
    case Lift(_)        => VType1
    case Irrelevant     => VType1

    case Meta(_)            => impossible()
    case Splice(_)          => impossible()
    case AppPruning(_, _)   => impossible()
    case IntLit(_)          => impossible()
    case Fix(_, _, _, _, _) => impossible()

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

  private def vapp0(f: Val0, a: Val0): Val0 = f match
    // case VLam0(f, b) =>
    //  f match
    //    case VPrim1(PFun, List(ta, tb)) => vlet0(ta, a, b)
    //    case _                          => impossible()
    case _ => VApp0(f, a)

  private def vproj0(v: Val0, p: ProjType, t: Val1): Val0 = (v, p) match
    // case (VPair0(fst, _, _), Fst) => fst
    // case (VPair0(_, snd, _), Snd) => snd
    case (p, Fst) => VFst0(t, p)
    case (p, Snd) => VSnd0(t, p)
    case _        => impossible()

  // flatten lets
  // let y : t2 ~> t3 = (let x : t1 ~> t2 = v; b1); b2
  // let x : t1 ~> t3 = v; let y = t2 ~> t3 = b1; b2
  // inline simple literals
  private def vlet0(
      t1: Val1,
      v: Val0,
      b: Val0 => Val0
  ): Val0 = v match
    // case VLet0(t3, v2, b2) =>
    // vlet0(t3, v2, w => vlet0(t1, b2(w), b))
    // case _ if isInlinable(v) => b(v)
    case _ => VLet0(t1, v, b)

  private def isInlinable(v: Val0): Boolean = v match
    case VVar0(_)                    => true
    case VGlobal0(_, _)              => true
    case VPrim0(_)                   => true
    case VIntLit0(_)                 => true
    case VSplicePrim0(PNil, List(_)) => true
    case _                           => false

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)             => vvar0(x)
    case Global(x)          => VGlobal0(x, eval1(getGlobal(x).get.ty)(Empty))
    case Prim(x)            => VPrim0(x)
    case Lam(x, _, fnty, b) => VLam0(eval1(fnty), clos0(b))
    case App(f, a, _)       => vapp0(eval0(f), eval0(a))
    case Proj(t, p, ty)     => vproj0(eval0(t), p, eval1(ty))
    case Let(x, t, STy, _, v, b) => vlet0(eval1(t), eval0(v), clos0(b))
    case Pair(fst, snd, ty)      => VPair0(eval0(fst), eval0(snd), eval1(ty))
    case Splice(t)               => vsplice0(eval1(t))
    case Wk(t)                   => eval0(t)(env.tail)
    case IntLit(n)               => VIntLit0(n)
    case Fix(go, x, t, b, a) =>
      VFix0(
        eval1(t),
        (v, w) => eval0(b)(Def0(Def0(env, v), w)),
        eval0(a)
      )

    case U(_)                  => impossible()
    case Pi(_, _, _, _)        => impossible()
    case Sigma(_, _, _)        => impossible()
    case Lift(_)               => impossible()
    case Meta(_)               => impossible()
    case Quote(_)              => impossible()
    case AppPruning(_, _)      => impossible()
    case Irrelevant            => impossible()
    case Let(_, _, _, _, _, _) => impossible()

  // quoting
  private def quoteVTy(v: Val1): IR.Ty = v match
    case VPrim1(PVoid, Nil)          => IR.TVoid
    case VPrim1(PUnitType, Nil)      => IR.TUnit
    case VPrim1(PBool, Nil)          => IR.TBool
    case VPrim1(PInt, Nil)           => IR.TInt
    case VPrim1(PPair, List(a, b))   => IR.TPair(quoteVTy(a), quoteVTy(b))
    case VPrim1(PList, List(t))      => IR.TList(quoteVTy(t))
    case VPrim1(PEither, List(a, b)) => IR.TEither(quoteVTy(a), quoteVTy(b))
    case _                           => impossible()

  private def quoteTy(v: Val1): IR.TDef = v match
    case VPrim1(PVal, List(t))    => IR.TDef(quoteVTy(t))
    case VPrim1(PFun, List(a, b)) => IR.TDef(quoteVTy(a), quoteTy(b))
    case _                        => IR.TDef(quoteVTy(v))

  private type NS = List[(IR.Name, IR.TDef)]
  private type Lets = List[(IR.Name, IR.TDef, IR.Comp)]
  private type Fresh = () => IR.Name
  private type Emit = () => (IR.GName, IR.Def => Unit)

  private def c2v(
      v: Val0
  )(implicit
      ns: NS,
      fresh: Fresh,
      emit: Emit
  ): (IR.Value, IR.TDef, Lets) =
    val (c, t, ds) = quoteComp(v)
    c match
      case IR.Val(qv) => (qv, t, ds)
      case _ =>
        val x = fresh()
        (IR.Var(x, t), t, ds ++ List((x, t, c)))

  private def quoteVal(
      v: Val0
  )(implicit
      ns: NS,
      fresh: Fresh,
      emit: Emit
  ): (IR.Value, IR.TDef, Lets) =
    v match
      case VVar0(k) =>
        val (x, t) = ns(k.toIx(mkLvl(ns.size)).expose)
        (IR.Var(x, t), t, Nil)
      case VGlobal0(x, ty) =>
        val t = quoteTy(ty)
        (IR.Global(x.expose, t), t, Nil)
      case VIntLit0(n) => (IR.IntLit(n), IR.TDef(IR.TInt), Nil)
      case VPair0(fst, snd, ty) =>
        val (f, tf, ds1) = quoteVal(fst)
        val (s, ts, ds2) = quoteVal(snd)
        (IR.Pair(tf.ty, ts.ty, f, s), quoteTy(ty), ds1 ++ ds2)
      case VPrim0(PUnit)  => (IR.Unit, IR.TDef(IR.TUnit), Nil)
      case VPrim0(PTrue)  => (IR.BoolLit(true), IR.TDef(IR.TBool), Nil)
      case VPrim0(PFalse) => (IR.BoolLit(false), IR.TDef(IR.TBool), Nil)
      case VSplicePrim0(PNil, List(t)) =>
        val ty = quoteVTy(t)
        (IR.LNil(ty), IR.TDef(IR.TList(ty)), Nil)
      case VSplicePrim0(PCons, List(t, hd, tl)) =>
        val ty = quoteVTy(t)
        val (qhd, _, ds1) = quoteVal(vsplice0(hd))
        val (qtl, _, ds2) = quoteVal(vsplice0(tl))
        (
          IR.LCons(ty, qhd, qtl),
          IR.TDef(IR.TList(ty)),
          ds1 ++ ds2
        )
      case VSplicePrim0(PLeft, List(t1, t2, v)) =>
        val ty1 = quoteVTy(t1)
        val ty2 = quoteVTy(t2)
        val (qv, _, ds) = quoteVal(vsplice0(v))
        (
          IR.ELeft(ty1, ty2, qv),
          IR.TDef(IR.TEither(ty1, ty2)),
          ds
        )
      case VSplicePrim0(PRight, List(t1, t2, v)) =>
        val ty1 = quoteVTy(t1)
        val ty2 = quoteVTy(t2)
        val (qv, _, ds) = quoteVal(vsplice0(v))
        (
          IR.ERight(ty1, ty2, qv),
          IR.TDef(IR.TEither(ty1, ty2)),
          ds
        )
      case _ => c2v(v)

  private def v2c(
      v: Val0
  )(implicit
      ns: NS,
      fresh: Fresh,
      emit: Emit
  ): (IR.Comp, IR.TDef, Lets) =
    val (qv, t, ds) = quoteVal(v)
    (IR.Val(qv), t, ds)

  private def quotePrim(p: PrimName): (IR.Op, IR.Ty) = p match
    case PPrimIntAdd => (IR.BAdd, IR.TInt)
    case PPrimIntMul => (IR.BMul, IR.TInt)
    case PPrimIntSub => (IR.BSub, IR.TInt)
    case PPrimIntDiv => (IR.BDiv, IR.TInt)
    case PPrimIntMod => (IR.BMod, IR.TInt)
    case PPrimIntEq  => (IR.BEq, IR.TBool)
    case PPrimIntNeq => (IR.BNeq, IR.TBool)
    case PPrimIntLt  => (IR.BLt, IR.TBool)
    case PPrimIntGt  => (IR.BGt, IR.TBool)
    case PPrimIntLeq => (IR.BLeq, IR.TBool)
    case PPrimIntGeq => (IR.BGeq, IR.TBool)
    case _           => impossible()

  private def quoteApp(v: Val0)(implicit
      ns: NS,
      fresh: Fresh,
      emit: Emit
  ): (IR.Comp, IR.TDef, Lets) =
    def go(
        v: Val0,
        as: List[IR.Value],
        ds: Lets
    ): (IR.Comp, IR.TDef, Lets) =
      v match
        case VApp0(f, a) =>
          val (qa, _, ds1) = quoteVal(a)
          go(f, qa :: as, ds1 ++ ds)
        case VPrim0(p) =>
          if as.size != 2 then impossible()
          val (op, rt) = quotePrim(p)
          (IR.BinOp(op, as(0), as(1)), IR.TDef(rt), ds)
        case v =>
          val (qv, ft, ds1) = quoteVal(v)
          (IR.App(qv, as), ft.drop(as.size), ds1 ++ ds)
    go(v, Nil, Nil)

  private def quoteLam(
      v: Val0,
      topTy: IR.TDef
  )(implicit ns: NS, fresh: Fresh, emit: Emit): (IR.Comp, IR.TDef, Lets) =
    def go(v: Val0, l: Lvl, ps: List[(IR.Name, IR.Ty)])(implicit
        ns: NS
    ): (IR.Comp, IR.TDef, Lets) = v match
      case VLam0(t, b) =>
        val td = quoteTy(t)
        val t1 = td.head
        val t2 = td.tail
        val x = fresh()
        go(b(VVar0(l)), l + 1, ps ++ List((x, t1)))((x, IR.TDef(t1)) :: ns)
      case b =>
        val qb = quoteLet(b)
        (IR.Lam(ps, topTy.drop(ps.size), qb), topTy, Nil)
    go(v, mkLvl(ns.size), Nil)

  private def appComp(
      e: IR.Comp,
      rt: IR.TDef,
      as: List[IR.Value]
  )(implicit fresh: Fresh, emit: Emit): (IR.Comp, Lets) =
    e match
      case IR.App(f, bs) => (IR.App(f, bs ++ as), Nil)
      case IR.Val(v)     => (IR.App(v, as), Nil)
      case _ =>
        val x = fresh()
        (IR.App(IR.Var(x, rt), as), List((x, rt, e)))

  private def etaExpandComp(
      td: IR.TDef,
      e: IR.Comp
  )(implicit
      fresh: Fresh,
      emit: Emit
  ): (List[(IR.Name, IR.Ty)], IR.Comp, Lets) =
    def go(
        ts: List[IR.Ty],
        e: IR.Comp,
        ps: List[(IR.Name, IR.Ty)]
    ): (List[(IR.Name, IR.Ty)], IR.Comp, Lets) =
      (ts, e) match
        case (ts, IR.Fix(_, _, _, _, _, _, _)) =>
          (ps, e, Nil)
        case (Nil, e) =>
          val (ea, ds) =
            appComp(
              e,
              td,
              ps.map((x, t) => IR.Var(x, IR.TDef(t)))
            )
          (ps, ea, ds)
        case (t :: ts, IR.Lam((x, _) :: Nil, bt, b)) =>
          val nps = ps ++ List((x, t))
          val (ps1, c, ds) = etaExpandComp(IR.TDef(ts, td.rt), b.body)
          (
            nps ++ ps1,
            c,
            b.ds.map((x, t, ps, v) =>
              (
                x,
                t,
                if ps.isEmpty then v
                else
                  IR.Lam(ps, t.drop(ps.size), IR.Let(Nil, t.drop(ps.size), v))
              )
            ) ++ ds
          )
        case (t :: ts, IR.Lam((x, _) :: lps, bt, b)) =>
          go(ts, IR.Lam(lps, bt, b), ps ++ List((x, t)))
        case (t :: ts, e) =>
          val x = fresh()
          go(ts, e, ps ++ List((x, t)))
    if td.ps.isEmpty then (Nil, e, Nil) else go(td.ps, e, Nil)

  private def etaExpand(
      td: IR.TDef,
      e: IR.Let
  )(implicit fresh: Fresh, emit: Emit): (List[(IR.Name, IR.Ty)], IR.Let) =
    val (ps, c, ds) = etaExpandComp(td, e.body)
    (ps, IR.Let(e.ds ++ expandLets(ds), e.ty.drop(ps.size), c))

  private def expandLets(ds: Lets)(implicit fresh: Fresh, emit: Emit): IR.Lets =
    ds.map { (x, t, e) =>
      if t.ps.isEmpty then (x, t.ty, e)
      else
        // eta expand and lift out
        val (gx, add) = emit()

        add(IR.DDef(gx, ))
    }

  private def quoteComp(
      v: Val0
  )(implicit
      ns: NS,
      fresh: Fresh,
      emit: Emit
  ): (IR.Comp, IR.TDef, Lets) =
    v match
      case VVar0(k)                              => v2c(v)
      case VGlobal0(x, ty)                       => v2c(v)
      case VIntLit0(n)                           => v2c(v)
      case VPair0(fst, snd, ty)                  => v2c(v)
      case VPrim0(PUnit)                         => v2c(v)
      case VPrim0(PTrue)                         => v2c(v)
      case VPrim0(PFalse)                        => v2c(v)
      case VSplicePrim0(PNil, List(t))           => v2c(v)
      case VSplicePrim0(PCons, List(t, hd, tl))  => v2c(v)
      case VSplicePrim0(PLeft, List(t1, t2, _))  => v2c(v)
      case VSplicePrim0(PRight, List(t1, t2, _)) => v2c(v)

      case VApp0(_, _) => quoteApp(v)
      case VFst0(ty, t) =>
        val qty = quoteVTy(ty)
        val (qt, _, ds) = quoteVal(t)
        (IR.Fst(qty, qt), IR.TDef(qty), ds)
      case VSnd0(ty, t) =>
        val qty = quoteVTy(ty)
        val (qt, _, ds) = quoteVal(t)
        (IR.Snd(qty, qt), IR.TDef(qty), ds)
      case VLam0(t, _) => quoteLam(v, quoteTy(t))
      case VLet0(t, v, b) =>
        val qt = quoteTy(t)
        val (qv, _, ds1) = quoteComp(v)
        val x = fresh()
        val (qb, qrt, ds2) =
          quoteComp(b(VVar0(mkLvl(ns.size))))((x, qt) :: ns, fresh, emit)
        (qb, qrt, ds1 ++ List((x, qt, qv)) ++ ds2)
      case VFix0(t, b, a) =>
        val qt = quoteTy(t)
        val t1 = qt.head
        val t2 = qt.tail
        val go = fresh()
        val x = fresh()
        val l = mkLvl(ns.size)
        val qb = quoteLet(b(VVar0(l), VVar0(l + 1)))(
          (x, IR.TDef(t1)) :: (go, qt) :: ns,
          fresh,
          emit
        )
        val (ps, qb2) = etaExpand(t2, qb)
        val (qa, _, ds) = quoteVal(a)
        (IR.Fix(t1, t2, go, x, ps, qb2, qa), t2, ds)

      case VSplicePrim0(PCaseBool, List(ty, b, t, f)) =>
        val qty = quoteVTy(ty)
        val (qb, _, ds) = quoteVal(vsplice0(b))
        val qt = quoteLet(vsplice0(t))
        val qf = quoteLet(vsplice0(f))
        (IR.If(qty, qb, qt, qf), IR.TDef(qty), ds)

      case VSplicePrim0(PCaseList, List(t1, t2, lst, n, c)) =>
        val qt1 = quoteVTy(t1)
        val qt2 = quoteVTy(t2)
        val (qlst, _, ds) = quoteVal(vsplice0(lst))
        // nil
        val qn = quoteLet(vsplice0(n))
        // cons
        val l = mkLvl(ns.size)
        val hd = fresh()
        val tl = fresh()
        val cc = vapp1(vapp1(c, VQuote1(VVar0(l))), VQuote1(VVar0(l + 1)))
        val qc = quoteLet(vsplice0(cc))(
          (tl, IR.TDef(IR.TList(qt1))) :: (hd, IR.TDef(qt1)) :: ns,
          fresh,
          emit
        )
        (IR.CaseList(qt1, qt2, qlst, qn, hd, tl, qc), IR.TDef(qt2), ds)

      case VSplicePrim0(PCaseEither, List(t1, t2, rt, v, l, r)) =>
        val qt1 = quoteVTy(t1)
        val qt2 = quoteVTy(t2)
        val qrt = quoteVTy(rt)
        val (qv, _, ds) = quoteVal(vsplice0(v))
        val lvl = mkLvl(ns.size)
        // left
        val x = fresh()
        val ll = vapp1(l, VQuote1(VVar0(lvl)))
        val ql = quoteLet(vsplice0(ll))((x, IR.TDef(qt1)) :: ns, fresh, emit)
        // right
        val y = fresh()
        val rr = vapp1(r, VQuote1(VVar0(lvl)))
        val qr = quoteLet(vsplice0(rr))((y, IR.TDef(qt2)) :: ns, fresh, emit)
        (IR.CaseEither(qt1, qt2, qrt, qv, x, ql, y, qr), IR.TDef(qrt), ds)

      case _ => impossible()

  private def quoteLet(
      v: Val0
  )(implicit ns: NS, fresh: Fresh, emit: Emit): IR.Let =
    val (b, t, ds) = quoteComp(v)
    IR.Let(expandLets(ds), t, b)

  // staging
  private def stageTDef(t: Ty): IR.TDef = quoteTy(eval1(t)(Empty))
  private def stageLet(t: Tm)(implicit fresh: Fresh, emit: Emit): IR.Let =
    quoteLet(eval0(t)(Empty))(Nil, fresh, emit)
  private def stageDef(d: Def): List[IR.Def] = d match
    case DDef(x, t, STy, v) =>
      var n = 0
      implicit val fresh: Fresh = () => {
        val c = n
        n += 1
        IR.Name(c)
      }
      var n2 = 0
      val nds = ArrayBuffer.empty[IR.Def]
      implicit val emit: Emit = () => {
        val c = n2
        n2 + 1
        (s"$x$$$c", d => { nds += d; () })
      }
      val ty = stageTDef(t)
      val (ps, b) = etaExpand(ty, stageLet(v))
      nds.toList ++ List(IR.DDef(x.expose, ty, ps, b))
    case _ => Nil

  def stage(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(stageDef))
