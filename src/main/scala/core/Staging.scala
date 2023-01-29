package core

import common.Common.*
import Syntax.*
import Globals.getGlobal

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
    case VPrim1(x: PrimName, args: List[Val1])
    case VLam1(fn: Val1 => Val1)
    case VQuote1(v: Val0)
    case VType1
    case VPair1(fst: Val1, snd: Val1)
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(x: Name, ty: Val1)
    case VPrim0(x: PrimName)
    case VSplicePrim0(x: PrimName, as: List[Val1])
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VLet0(ty: Val1, value: Val0, body: Val0 => Val0)
    case VPair0(fst: Val0, snd: Val0, ty: Val1)
    case VFst0(ty: Val1, t: Val0)
    case VSnd0(ty: Val1, t: Val0)
    case VIntLit0(n: Int)
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
    case (VPrim1(x, as), _)       => VPrim1(x, as ++ List(a))
    case (VQuote1(f), VQuote1(a)) => VQuote1(vapp0(f, a))
    case _                        => impossible()

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
    case Proj(t, p, _)         => vproj1(eval1(t), p)
    case Let(_, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case Pair(fst, snd, _)     => VPair1(eval1(fst), eval1(snd))
    case Quote(t)              => VQuote1(eval0(t))
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

  private def vapp0(f: Val0, a: Val0): Val0 = f match
    case VLam0(f, b) =>
      f match
        case VPrim1(PTFun, List(ta, _, _)) => vlet0(ta, a, b)
        case _                             => impossible()
    case _ => VApp0(f, a)

  private def vproj0(v: Val0, p: ProjType, t: Val1): Val0 = (v, p) match
    case (VPair0(fst, _, _), Fst) => fst
    case (VPair0(_, snd, _), Snd) => snd
    case (p, Fst)                 => VFst0(t, p)
    case (p, Snd)                 => VSnd0(t, p)
    case _                        => impossible()

  private def vlet0(
      t1: Val1,
      v: Val0,
      b: Val0 => Val0
  ): Val0 = v match
    case VLet0(t3, v2, b2)   => vlet0(t3, v2, w => vlet0(t1, b2(w), b))
    case _ if isInlinable(v) => b(v)
    case _                   => VLet0(t1, v, b)

  private def isInlinable(v: Val0): Boolean = v match
    case VVar0(_)       => true
    case VGlobal0(_, _) => true
    case VPrim0(_)      => true
    case VIntLit0(_)    => true
    case _              => false

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)                => vvar0(x)
    case Global(x)             => VGlobal0(x, eval1(getGlobal(x).get.ty)(Empty))
    case Prim(x)               => VPrim0(x)
    case Lam(x, _, fnty, b)    => VLam0(eval1(fnty), clos0(b))
    case App(f, a, _)          => vapp0(eval0(f), eval0(a))
    case Proj(t, p, ty)        => vproj0(eval0(t), p, eval1(ty))
    case Let(x, t, _, _, v, b) => vlet0(eval1(t), eval0(v), clos0(b))
    case Pair(fst, snd, ty)    => VPair0(eval0(fst), eval0(snd), eval1(ty))
    case Splice(t)             => vsplice0(eval1(t))
    case Wk(t)                 => eval0(t)(env.tail)
    case IntLit(n)             => VIntLit0(n)
    case _                     => impossible()

  // quotation
  private def quoteVTy(v: Val1): Ty = v match
    case VPrim1(PUnitType, Nil) => Prim(PUnitType)
    case VPrim1(PBool, Nil)     => Prim(PBool)
    case VPrim1(PInt, Nil)      => Prim(PInt)
    case VPrim1(PTPair, List(a, b)) =>
      App(App(Prim(PTPair), quoteVTy(a), Expl), quoteVTy(b), Expl)
    case _ => impossible()

  private def quoteFTy(v: Val1): Ty = v match
    case VPrim1(PTFun, List(a, _, b)) =>
      App(App(Prim(PTFun), quoteVTy(a), Expl), quoteFTy(b), Expl)
    case _ => quoteVTy(v)

  private def primOverApp(p: PrimName, n: Int, as: List[Val1])(implicit
      l: Lvl
  ): Tm =
    val hd = quoteExpr(VSplicePrim0(p, as.take(n)))
    val qas = as.drop(n).map(a => quoteExpr(vsplice0(a)))
    qas.foldLeft(hd)((f, a) => App(f, a, Expl))
  private def quoteExpr(v: Val0)(implicit l: Lvl): Tm = v match
    case VVar0(lvl)     => Var(lvl.toIx)
    case VGlobal0(x, _) => Global(x)
    case VPrim0(x)      => Prim(x)
    case VApp0(f, a)    => App(quoteExpr(f), quoteExpr(a), Expl)
    case VLam0(ft, b) =>
      Lam(DoBind(Name("x")), Expl, quoteFTy(ft), quoteExpr(b(VVar0(l)))(l + 1))
    case VLet0(ty, v, b) =>
      Let(
        Name("x"),
        quoteFTy(ty),
        STy(Irrelevant),
        Irrelevant,
        quoteExpr(v),
        quoteExpr(b(VVar0(l)))(l + 1)
      )
    case VPair0(fst, snd, ty) =>
      Pair(quoteExpr(fst), quoteExpr(snd), quoteVTy(ty))
    case VFst0(ty, t) => Proj(quoteExpr(t), Fst, quoteVTy(ty))
    case VSnd0(ty, t) => Proj(quoteExpr(t), Snd, quoteVTy(ty))
    case VIntLit0(n)  => IntLit(n)

    case VSplicePrim0(PFix, List(pty, _, rty, b)) =>
      val qpty = quoteVTy(pty)
      val qfty = quoteFTy(rty)
      val qb = Lam(
        DoBind(Name("go")),
        Expl,
        Irrelevant,
        Lam(
          DoBind(Name("x")),
          Expl,
          Irrelevant,
          quoteExpr(
            vsplice0(vapp1(vapp1(b, VQuote1(VVar0(l))), VQuote1(VVar0(l + 1))))
          )(
            l + 2
          )
        )
      )
      App(App(App(Prim(PFix), qpty, Impl), qfty, Impl), qb, Expl)
    case VSplicePrim0(PFix, as) => primOverApp(PFix, 4, as)

    case VSplicePrim0(PCaseBool, List(_, ty, b, t, f)) =>
      val qty = quoteFTy(ty)
      val qb = quoteExpr(vsplice0(b))
      val qt = quoteExpr(vsplice0(t))
      val qf = quoteExpr(vsplice0(f))
      App(
        App(App(App(Prim(PCaseBool), qty, Impl), qb, Expl), qt, Expl),
        qf,
        Expl
      )
    case VSplicePrim0(PCaseBool, as) => primOverApp(PCaseBool, 5, as)

    case _ => impossible()

  // staging
  private def stageFTy(t: Ty): Ty = quoteFTy(eval1(t)(Empty))

  private def stageExpr(t: Tm): Tm = quoteExpr(eval0(t)(Empty))(lvl0)

  private def stageDef(d: Def): List[Def] = d match
    case DDef(x, t, st @ STy(_), v) =>
      List(DDef(x, stageFTy(t), st, stageExpr(v)))
    case _ => Nil

  def stage(ds: Defs): Defs = Defs(ds.toList.flatMap(stageDef))
