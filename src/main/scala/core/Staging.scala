package core

import common.Common.*
import Syntax.*
import Globals.getGlobal
import ir.Syntax as IR

import scala.annotation.tailrec

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
    case VGlobal0(x: Name)
    case VPrim0(x: PrimName)
    case VApp0(f: Val0, a: Val0)
    case VLam0(x: Bind, fnty: Val1, body: Val0 => Val0)
    case VFix0(
        go: Name,
        x: Name,
        fnty: Val1,
        body: (Val0, Val0) => Val0,
        arg: Val0
    )
    case VLet0(x: Name, ty: Val1, bty: Val1, value: Val0, body: Val0 => Val0)
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

  private def vbool0(b: Boolean): Val0 =
    if b then VPrim0(PTrue) else VPrim0(PFalse)

  private def vapp0(f: Val0, a: Val0): Val0 = f match
    case VLam0(DontBind, _, b) => b(a)
    case _                     => VApp0(f, a)

  private def vproj0(v: Val0, p: ProjType, t: Val1): Val0 = (v, p) match
    case (VPair0(fst, _, _), Fst) => fst
    case (VPair0(_, snd, _), Snd) => snd
    case (p, Fst)                 => VFst0(t, p)
    case (p, Snd)                 => VSnd0(t, p)
    case _                        => impossible()

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)             => vvar0(x)
    case Global(x)          => VGlobal0(x)
    case Prim(x)            => VPrim0(x)
    case Lam(x, _, fnty, b) => VLam0(x, eval1(fnty), clos0(b))
    case App(f, a, _)       => vapp0(eval0(f), eval0(a))
    case Proj(t, p, ty)     => vproj0(eval0(t), p, eval1(ty))
    case Let(x, t, vf, bt, v, b) =>
      VLet0(x, eval1(t), eval1(bt), eval0(v), clos0(b))
    case Pair(fst, snd, ty) => VPair0(eval0(fst), eval0(snd), eval1(ty))
    case Splice(t)          => vsplice0(eval1(t))
    case Wk(t)              => eval0(t)(env.tail)
    case IntLit(n)          => VIntLit0(n)
    case Fix(go, x, t, b, a) =>
      VFix0(
        go,
        x,
        eval1(t),
        (v, w) => eval0(b)(Def0(Def0(env, v), w)),
        eval0(a)
      )

    case U(_)             => impossible()
    case Pi(_, _, _, _)   => impossible()
    case Sigma(_, _, _)   => impossible()
    case Lift(_)          => impossible()
    case Meta(_)          => impossible()
    case Quote(_)         => impossible()
    case AppPruning(_, _) => impossible()
    case Irrelevant       => impossible()

  private def quoteVTy(v: Val1)(implicit l: Lvl): IR.Ty = v match
    case VPrim1(PVoid, Nil)          => IR.TVoid
    case VPrim1(PUnitType, Nil)      => IR.TUnit
    case VPrim1(PBool, Nil)          => IR.TBool
    case VPrim1(PInt, Nil)           => IR.TInt
    case VPrim1(PPair, List(a, b))   => IR.TPair(quoteVTy(a), quoteVTy(b))
    case VPrim1(PList, List(t))      => IR.TList(quoteVTy(t))
    case VPrim1(PEither, List(a, b)) => IR.TEither(quoteVTy(a), quoteVTy(b))
    case _                           => impossible()

  private def quoteTy(v: Val1)(implicit l: Lvl): IR.TDef = v match
    case VPrim1(PVal, List(t))    => IR.TDef(quoteVTy(t))
    case VPrim1(PFun, List(a, b)) => IR.TDef(quoteVTy(a), quoteTy(b))
    case _                        => impossible()

  private def fresh()(implicit ns: List[(IR.Name, IR.TDef)]): IR.Name =
    IR.Name.fresh(ns.map(_._1))

  private def quoteApp(v: Val0, b: IR.Expr)(implicit
      l: Lvl,
      ns: List[(IR.Name, IR.TDef)]
  ): IR.Expr = v match
    case VApp0(VPrim0(p), a) => IR.BinOp(quotePrim(p), quoteExpr(a), b)
    case VPrim0(p) =>
      val x = fresh()
      val op = quotePrim(p)
      IR.Lam(
        x,
        IR.TInt,
        IR.TDef(op.returnTy),
        IR.BinOp(op, b, IR.Var(x, IR.TDef(IR.TInt)))
      )
    case f => IR.App(quoteExpr(f), b)

  private def quotePrim(p: PrimName): IR.Op = p match
    case PPrimIntAdd => IR.BAdd
    case PPrimIntMul => IR.BMul
    case PPrimIntSub => IR.BSub
    case PPrimIntDiv => IR.BDiv
    case PPrimIntMod => IR.BMod
    case PPrimIntEq  => IR.BEq
    case PPrimIntNeq => IR.BNeq
    case PPrimIntLt  => IR.BLt
    case PPrimIntGt  => IR.BGt
    case PPrimIntLeq => IR.BLeq
    case PPrimIntGeq => IR.BGeq
    case _           => impossible()

  private def quoteExpr(
      v: Val0
  )(implicit l: Lvl, ns: List[(IR.Name, IR.TDef)]): IR.Expr = v match
    case VVar0(k) =>
      val (x, t) = ns(k.toIx.expose)
      IR.Var(x, t)
    case VGlobal0(x) =>
      IR.Global(x.expose, quoteTy(eval1(getGlobal(x).get.ty)(Empty)))
    case VApp0(f, a) => quoteApp(f, quoteExpr(a))
    case VLam0(_, fnty, b) =>
      val x = fresh()
      val td = quoteTy(fnty)
      val at = td.ps.head
      IR.Lam(
        x,
        at,
        IR.TDef(td.ps.tail, td.rt),
        quoteExpr(b(VVar0(l)))(l + 1, (x, IR.TDef(at)) :: ns)
      )
    case VLet0(_, ty, bty, v, b) =>
      val x = fresh()
      val td = quoteTy(ty)
      IR.Let(
        x,
        td,
        quoteTy(bty),
        quoteExpr(v),
        quoteExpr(b(VVar0(l)))(l + 1, (x, td) :: ns)
      )
    case VFix0(_, _, t, b, a) =>
      val go = fresh()
      val td = quoteTy(t)
      val at = td.ps.head
      val atd = IR.TDef(at)
      val x = fresh()((go, atd) :: ns)
      IR.Fix(
        go,
        x,
        at,
        IR.TDef(td.ps.tail, td.rt),
        quoteExpr(b(VVar0(l), VVar0(l + 1)))(l + 2, (x, atd) :: (go, td) :: ns),
        quoteExpr(a)
      )

    case VPair0(fst, snd, ty) =>
      quoteVTy(ty) match
        case IR.TPair(t1, t2) => IR.Pair(t1, t2, quoteExpr(fst), quoteExpr(snd))
        case _                => impossible()
    case VFst0(ty, t) => IR.Fst(quoteVTy(ty), quoteExpr(t))
    case VSnd0(ty, t) => IR.Snd(quoteVTy(ty), quoteExpr(t))

    case VIntLit0(n) => IR.IntLit(n)

    case VPrim0(PUnit)  => IR.Unit
    case VPrim0(PTrue)  => IR.BoolLit(true)
    case VPrim0(PFalse) => IR.BoolLit(false)

    case VSplicePrim0(PAbsurd, List(_, t, _)) => IR.Absurd(quoteTy(t))
    case VSplicePrim0(PCaseBool, List(_, _, VQuote1(VPrim0(PTrue)), t, _)) =>
      quoteExpr(vsplice0(t))
    case VSplicePrim0(PCaseBool, List(_, _, VQuote1(VPrim0(PFalse)), _, f)) =>
      quoteExpr(vsplice0(f))
    case VSplicePrim0(PCaseBool, List(ty, b, t, f)) =>
      val cond = quoteExpr(vsplice0(b))
      val ifTrue = quoteExpr(vsplice0(t))
      val ifFalse = quoteExpr(vsplice0(f))
      IR.If(IR.TDef(quoteVTy(ty)), cond, ifTrue, ifFalse)

    case VSplicePrim0(PNil, List(t)) => IR.LNil(quoteVTy(t))
    case VSplicePrim0(PCons, List(t, hd, tl)) =>
      IR.LCons(quoteVTy(t), quoteExpr(vsplice0(hd)), quoteExpr(vsplice0(tl)))
    case VSplicePrim0(PCaseList, List(t1, t2, lst, n, c)) =>
      val hd = fresh()
      val et = quoteVTy(t1)
      val etd = IR.TDef(et)
      val tl = fresh()((hd, etd) :: ns)
      val cc = vapp1(vapp1(c, VQuote1(VVar0(l))), VQuote1(VVar0(l + 1)))
      val cr = quoteExpr(vsplice0(cc))(
        l + 2,
        (tl, IR.TDef(IR.TList(et))) :: (hd, etd) :: ns
      )
      IR.CaseList(
        et,
        IR.TDef(quoteVTy(t2)),
        quoteExpr(vsplice0(lst)),
        quoteExpr(vsplice0(n)),
        hd,
        tl,
        cr
      )

    case VSplicePrim0(PLeft, List(t1, t2, v)) =>
      IR.ELeft(quoteVTy(t1), quoteVTy(t2), quoteExpr(vsplice0(v)))
    case VSplicePrim0(PRight, List(t1, t2, v)) =>
      IR.ERight(quoteVTy(t1), quoteVTy(t2), quoteExpr(vsplice0(v)))
    case VSplicePrim0(PCaseEither, List(t1q, t2q, rtq, v, lc, rc)) =>
      val t1 = quoteVTy(t1q)
      val t1d = IR.TDef(t1)
      val t2 = quoteVTy(t2q)
      val t2d = IR.TDef(t2)
      val rt = quoteTy(rtq)

      val x = fresh()
      val clc = vapp1(lc, VQuote1(VVar0(l)))
      val clcq = quoteExpr(vsplice0(clc))(l + 1, (x, t1d) :: ns)
      val crc = vapp1(rc, VQuote1(VVar0(l)))
      val crcq = quoteExpr(vsplice0(crc))(l + 1, (x, t2d) :: ns)
      IR.CaseEither(
        t1,
        t2,
        rt,
        quoteExpr(vsplice0(v)),
        x,
        clcq,
        x,
        crcq
      )

    case VPrim0(p) =>
      val x = fresh()
      val dty = IR.TDef(IR.TInt)
      val y = fresh()((x, dty) :: ns)
      val op = quotePrim(p)
      IR.Lam(
        x,
        IR.TInt,
        IR.TDef(IR.TInt, op.returnTy),
        IR.Lam(
          y,
          IR.TInt,
          IR.TDef(op.returnTy),
          IR.BinOp(op, IR.Var(x, dty), IR.Var(y, dty))
        )
      )

    case _ => impossible()

  private def stageExpr(t: Tm): IR.Expr = quoteExpr(eval0(t)(Empty))(lvl0, Nil)
  private def stageTDef(t: Ty): IR.TDef = quoteTy(eval1(t)(Empty))(lvl0)
  private def stageDef(d: Def): Option[IR.Def] = d match
    case DDef(x, t, STy, v) =>
      Some(IR.DDef(x.expose, stageTDef(t), stageExpr(v)))
    case _ => None

  def stage(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(stageDef))
