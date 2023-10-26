package ir

import common.Common.*
import common.Ref
import core.Syntax as S
import Syntax.*
import core.Globals.*
import core.Value.*
import core.Evaluation.{stage, forceAll1, eval1}

import scala.collection.mutable

object Monomorphize:
  // t should be staged
  def monomorphize(t: S.Tm0)(implicit ref: Ref[LName]): Tm = go(t)(ref, Nil)._1

  def monomorphize(t: S.Ty): TDef = goTDef(t)

  type Ctx = List[(LName, TDef)]

  private def go(t: S.Tm0)(implicit ref: Ref[LName], ctx: Ctx): (Tm, TDef) =
    t match
      case S.Var0(ix) =>
        val (x, ty) = ctx(ix.expose)
        (Var(x, ty), ty)
      case S.Global0(x) =>
        getGlobal(x) match
          case Some(GlobalEntry0(_, _, ty, _, _, _, _)) =>
            val td = goTDef(ty)
            (Global(x, td), td)
          case _ => impossible()
      case S.Impossible(ty) =>
        val td = goTDef(ty)
        (Impossible(td), td)

      case S.App0(fn, arg) =>
        val (ef, tf) = go(fn)
        val (ea, ta) = go(arg)
        (App(ef, ea), tf.tail)
      case S.Con(name, ty, args) =>
        val dt = goTy(ty)
        (Con(name, dt, args.map(a => go(a)._1)), TDef(dt))
      case S.Wk10(tm) => go(tm)
      case S.Wk00(tm) => go(tm)(ref, ctx.tail)

      case S.Lam0(_, ty, b) =>
        val x = fresh()
        val ta = goTy(ty)
        val (eb, bty) = go(b)(ref, (x, TDef(ta)) :: ctx)
        (Lam(x, ta, bty, eb), TDef(ta, bty))
      case S.Let0(_, ty, v, b) =>
        val x = fresh()
        val tv = goTDef(ty)
        val (ev, _) = go(v)
        val (eb, tb) = go(b)(ref, (x, tv) :: ctx)
        (Let(x, tv, tb, ev, eb), tb)
      case S.LetRec(_, ty, v, b) =>
        val x = fresh()
        val tv = goTDef(ty)
        val (ev, _) = go(v)(ref, (x, tv) :: ctx)
        val (eb, tb) = go(b)(ref, (x, tv) :: ctx)
        (LetRec(x, tv, tb, ev, eb), tb)
      case S.Match(s, t, c, ps, b, o) =>
        val x = fresh()
        val dt = goTy(t)
        val (es, _) = go(s)
        val vx = Var(x, TDef(dt))
        val eb =
          (0 until ps.size).zip(ps).foldLeft(go(b)._1) { case (v, (i, t)) =>
            App(v, Field(vx, goTy(t), i))
          }
        val (eo, to) = go(o)
        (Match(es, dt, to, c, x, eb, eo), to)

      case S.Splice(tm)  => impossible()
      case S.Prim0(name) => impossible()

  private inline def fresh()(implicit ref: Ref[LName]): LName =
    ref.updateGetOld(_ + 1)

  // monomorphization
  type DatatypeCons = List[(Name, List[(Bind, Ty)])]
  type Datatype = (Name, DatatypeCons)
  private val monoMap: mutable.Map[(Name, List[Ty]), Name] =
    mutable.Map.empty
  private val monoData: mutable.ArrayBuffer[Datatype] =
    mutable.ArrayBuffer.empty

  private inline def goTDef(t: S.Ty): TDef = goVTDef(eval1(t)(EEmpty))
  private def goVTDef(t: VTy): TDef = forceAll1(t) match
    case VFun(pty, _, rty) => TDef(goVTy(pty), goVTDef(rty))
    case t                 => TDef(goVTy(t))

  private inline def goTy(t: S.Ty, env: Env = EEmpty): Ty = goVTy(eval1(t)(env))
  private def goVTy(t: VTy): Ty = forceAll1(t) match
    case VTCon(dx, ps) => TCon(mono(dx, ps))
    case _             => impossible()

  private def genName(dx: Name, ps: List[Ty]): Name =
    if ps.isEmpty then dx
    else
      val gps = ps.map(genName).mkString("_")
      Name(s"${dx}_$gps")
  private def genName(t: Ty): Name = t match
    case TCon(dx) => dx

  private def mono(dx: Name, ps: List[VTy]): Name =
    val mps = ps.map(goVTy)
    monoMap.get((dx, mps)) match
      case Some(x) => x
      case None =>
        val x = genName(dx, mps)
        monoMap += (dx, mps) -> x
        monoData += ((x, monoCons(dx, ps)))
        x

  private def monoCons(dx: Name, ps: List[VTy]): DatatypeCons =
    val env = ps.foldLeft(EEmpty)(E1.apply)
    getGlobalData0(dx).cons.map { cx =>
      val ps = getGlobalCon0(cx).params.map((x, t) => (x, goTy(t, env)))
      (cx, ps)
    }

  def monomorphizedDatatypes: List[Datatype] = monoData.toList
