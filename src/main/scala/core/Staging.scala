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
    case VFunTy1(pt: Val1, vf: Val1, rt: Val1)
    case VPairTy1(pt: Val1, rt: Val1)
    case VPair1(fst: Val1, snd: Val1)
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(x: Name)
    case VPrim0(x: PrimName)
    case VApp0(f: Val0, a: Val0)
    case VLam0(x: Bind, body: Val0 => Val0)
    case VLet0(x: Name, ty: Val1, value: Val0, body: Val0 => Val0)
    case VPair0(fst: Val0, snd: Val0)
    case VFst0(t: Val0)
    case VSnd0(t: Val0)
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

  private def clos1(t: Tm)(implicit env: Env): Val1 => Val1 =
    v => eval1(t)(Def1(env, v))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Var(x)             => vvar1(x)
    case Global(x)          => eval1(getGlobal(x).get.tm)
    case Prim(x)            => VPrim1(x, Nil)
    case Lam(_, _, b)       => VLam1(clos1(b))
    case App(f, a, _)       => vapp1(eval1(f), eval1(a))
    case Proj(t, p)         => vproj1(eval1(t), p)
    case Let(_, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case Pair(fst, snd)     => VPair1(eval1(fst), eval1(snd))
    case Quote(t)           => VQuote1(eval0(t))
    case Wk(t)              => eval1(t)(env.tail)

    case FunTy(pt, vf, rt) => VFunTy1(eval1(pt), eval1(vf), eval1(rt))
    case PairTy(pt, rt)    => VPairTy1(eval1(pt), eval1(rt))

    case U(_)           => VType1
    case Pi(_, _, _, _) => VType1
    case Sigma(_, _, _) => VType1
    case Lift(_, _)     => VType1

    case Meta(_)          => impossible()
    case Splice(_)        => impossible()
    case AppPruning(_, _) => impossible()
    case IntLit(_)        => impossible()

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

  private def vbinop0(op: PrimName, a: Val0, b: Val0): Val0 = (op, a, b) match
    case (PPrimIntAdd, VIntLit0(a), VIntLit0(b)) => VIntLit0(a + b)
    case (PPrimIntMul, VIntLit0(a), VIntLit0(b)) => VIntLit0(a * b)
    case (PPrimIntSub, VIntLit0(a), VIntLit0(b)) => VIntLit0(a - b)
    case (PPrimIntDiv, VIntLit0(a), VIntLit0(b)) => VIntLit0(a / b)
    case (PPrimIntMod, VIntLit0(a), VIntLit0(b)) => VIntLit0(a % b)
    case (PPrimIntEq, VIntLit0(a), VIntLit0(b))  => vbool0(a == b)
    case (PPrimIntNeq, VIntLit0(a), VIntLit0(b)) => vbool0(a != b)
    case (PPrimIntLt, VIntLit0(a), VIntLit0(b))  => vbool0(a < b)
    case (PPrimIntGt, VIntLit0(a), VIntLit0(b))  => vbool0(a > b)
    case (PPrimIntLeq, VIntLit0(a), VIntLit0(b)) => vbool0(a <= b)
    case (PPrimIntGeq, VIntLit0(a), VIntLit0(b)) => vbool0(a >= b)

    case (PPrimIntAdd, VIntLit0(0), v) => v
    case (PPrimIntAdd, v, VIntLit0(0)) => v

    case (PPrimIntMul, VIntLit0(0), v) => VIntLit0(0)
    case (PPrimIntMul, v, VIntLit0(0)) => VIntLit0(0)
    case (PPrimIntMul, VIntLit0(1), v) => v
    case (PPrimIntMul, v, VIntLit0(1)) => v

    case (PPrimIntSub, v, VIntLit0(0)) => v
    case (PPrimIntDiv, v, VIntLit0(1)) => v

    case (op, a, b) => VApp0(VApp0(VPrim0(op), a), b)

  private def vapp0(f: Val0, a: Val0): Val0 = f match
    case VLam0(DontBind, b)               => b(a)
    case VLam0(DoBind(x), b)              => VLet0(x, VType1, a, b)
    case VApp0(VPrim0(p), b) if p.isBinOp => vbinop0(p, b, a)
    case _                                => VApp0(f, a)

  private def vproj0(v: Val0, p: ProjType): Val0 = (v, p) match
    case (VPair0(fst, _), Fst)         => fst
    case (VPair0(_, snd), Snd)         => snd
    case (VPair0(fst, _), Named(_, 0)) => fst
    case (VPair0(_, snd), Named(x, i)) => vproj0(snd, Named(x, i - 1))
    case (p, Fst)                      => VFst0(p)
    case (p, Snd)                      => VSnd0(p)
    case (p, Named(_, 0))              => VFst0(p)
    case (p, Named(x, i))              => vproj0(VSnd0(p), Named(x, i - 1))

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)       => vvar0(x)
    case Global(x)    => VGlobal0(x)
    case Prim(x)      => VPrim0(x)
    case Lam(x, _, b) => VLam0(x, clos0(b))
    case App(f, a, _) => vapp0(eval0(f), eval0(a))
    case Proj(t, p)   => vproj0(eval0(t), p)
    case Let(x, t, vf, v, b) =>
      VLet0(x, eval1(t), eval0(v), clos0(b))
    case Pair(fst, snd) => VPair0(eval0(fst), eval0(snd))
    case Splice(t)      => vsplice0(eval1(t))
    case Wk(t)          => eval0(t)(env.tail)
    case IntLit(n)      => VIntLit0(n)

    case FunTy(pt, vf, rt) => impossible()
    case PairTy(pt, rt)    => impossible()
    case U(_)              => impossible()
    case Pi(_, _, _, _)    => impossible()
    case Sigma(_, _, _)    => impossible()
    case Lift(_, _)        => impossible()
    case Meta(_)           => impossible()
    case Quote(_)          => impossible()
    case AppPruning(_, _)  => impossible()

  private def quoteType(v: Val1)(implicit l: Lvl): IR.Type = v match
    case VPrim1(PVoid, Nil)     => IR.TVoid
    case VPrim1(PUnitType, Nil) => IR.TUnit
    case VPrim1(PBool, Nil)     => IR.TBool
    case VPrim1(PInt, Nil)      => IR.TInt
    case VPairTy1(fst, snd)     => IR.TPair(quoteType(fst), quoteType(snd))
    case _                      => impossible()

  private def quoteTDef(v: Val1)(implicit l: Lvl): IR.TDef =
    @tailrec
    def go(v: Val1, ps: List[IR.Type]): IR.TDef = v match
      case VFunTy1(pt, _, rt) => go(rt, ps ++ List(quoteType(pt)))
      case t                  => IR.TDef(ps, quoteType(t))
    go(v, Nil)

  @tailrec
  private def quoteLam(v: Val0, ps: List[IR.Name] = Nil)(implicit
      l: Lvl,
      ns: List[IR.Name]
  ): IR.Expr = v match
    case VLam0(_, b) =>
      val x = IR.Name.fresh
      quoteLam(b(VVar0(l)), ps ++ List(x))(l + 1, x :: ns)
    case b => IR.Lam(ps, quoteExpr(b))

  @tailrec
  private def quoteApp(v: Val0, as: List[IR.Expr] = Nil)(implicit
      l: Lvl,
      ns: List[IR.Name]
  ): IR.Expr = v match
    case VApp0(f, a)         => quoteApp(f, quoteExpr(a) :: as)
    case VPrim0(PPrimIntAdd) => IR.BinOp(IR.BAdd, as(0), as(1))
    case VPrim0(PPrimIntMul) => IR.BinOp(IR.BMul, as(0), as(1))
    case VPrim0(PPrimIntSub) => IR.BinOp(IR.BSub, as(0), as(1))
    case VPrim0(PPrimIntDiv) => IR.BinOp(IR.BDiv, as(0), as(1))
    case VPrim0(PPrimIntMod) => IR.BinOp(IR.BMod, as(0), as(1))
    case VPrim0(PPrimIntEq)  => IR.BinOp(IR.BEq, as(0), as(1))
    case VPrim0(PPrimIntNeq) => IR.BinOp(IR.BNeq, as(0), as(1))
    case VPrim0(PPrimIntLt)  => IR.BinOp(IR.BLt, as(0), as(1))
    case VPrim0(PPrimIntGt)  => IR.BinOp(IR.BGt, as(0), as(1))
    case VPrim0(PPrimIntLeq) => IR.BinOp(IR.BLeq, as(0), as(1))
    case VPrim0(PPrimIntGeq) => IR.BinOp(IR.BGeq, as(0), as(1))
    case f                   => IR.App(quoteExpr(f), as)

  private def quoteExpr(
      v: Val0
  )(implicit l: Lvl, ns: List[IR.Name]): IR.Expr = v match
    case VVar0(k)    => IR.Var(ns(k.toIx.expose))
    case VGlobal0(x) => IR.Global(x.expose)
    case VApp0(_, _) => quoteApp(v)
    case VLam0(_, _) => quoteLam(v)
    case VLet0(_, ty, v, b) =>
      val x = IR.Name.fresh
      IR.Let(x, quoteExpr(v), quoteExpr(b(VVar0(l)))(l + 1, x :: ns))

    case VPair0(fst, snd) => IR.Pair(quoteExpr(fst), quoteExpr(snd))
    case VFst0(t)         => IR.Fst(quoteExpr(t))
    case VSnd0(t)         => IR.Snd(quoteExpr(t))

    case VIntLit0(n) => IR.IntLit(n)

    case VPrim0(PUnit)  => IR.Unit
    case VPrim0(PTrue)  => IR.BoolLit(true)
    case VPrim0(PFalse) => IR.BoolLit(false)

    case VSplicePrim0(PAbsurd, List(_, _)) => IR.Absurd
    case VSplicePrim0(PElimBool, List(_, t, _, VQuote1(VPrim0(PTrue)))) =>
      quoteExpr(vsplice0(t))
    case VSplicePrim0(PElimBool, List(_, _, f, VQuote1(VPrim0(PFalse)))) =>
      quoteExpr(vsplice0(f))
    case VSplicePrim0(PElimBool, List(_, t, f, b)) =>
      val cond = quoteExpr(vsplice0(b))
      val ifTrue = quoteExpr(vsplice0(t))
      val ifFalse = quoteExpr(vsplice0(f))
      IR.If(cond, ifTrue, ifFalse)

    case _ => impossible()

  private def stageExpr(t: Tm): IR.Expr = quoteExpr(eval0(t)(Empty))(lvl0, Nil)
  private def stageTDef(t: Ty): IR.TDef = quoteTDef(eval1(t)(Empty))(lvl0)
  private def stageDef(d: Def): Option[IR.Def] = d match
    case DDef(x, t, S0(_), v) =>
      Some(IR.DDef(x.expose, stageTDef(t), stageExpr(v)))
    case _ => None

  def stage(ds: Defs): IR.Defs = IR.Defs(ds.toList.flatMap(stageDef))
