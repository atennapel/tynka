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
  // t will be monomorphized and eta-expanded
  def monomorphize(t: S.Tm0)(implicit ref: Ref[LName]): Tm =
    val (tm, ty) = go(t)(ref, Nil)
    val (vs, rt, spine) = eta(ty)
    tm.apps(spine).lams(vs, rt)

  def monomorphize(t: S.Ty): TDef = goTDef(t)

  type Ctx = List[(LName, TDef)]

  private def go(t: S.Tm0)(implicit ref: Ref[LName], ctx: Ctx): (Tm, TDef) =
    t match
      case S.IntLit(v) => (IntLit(v), TDef(TPrim(Name("Int"))))
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
        val dt = goTy(ty): @unchecked
        val TCon(dx) = dt: @unchecked
        (Con(dx, name, args.map(a => go(a)._1)), TDef(dt))
      case S.Wk10(tm) => go(tm)
      case S.Wk00(tm) => go(tm)(ref, ctx.tail)

      case S.Lam0(_, ty, b) =>
        val x = fresh()
        val ta = goTy(ty)
        val (eb, bty) = go(b)(ref, (x, TDef(ta)) :: ctx)
        val (vs, rt, spine) = eta(bty)
        (eb.apps(spine).lams((x, ta) :: vs, rt), TDef(ta, bty))
      case S.Let0(_, ty, v, b) =>
        val x = fresh()
        val tv = goTDef(ty)
        val (vvs, vrt, vspine) = eta(tv)
        val (ev, _) = go(v)
        val (eb, tb) = go(b)(ref, (x, tv) :: ctx)
        val (vs, rt, spine) = eta(tb)
        (
          Let(x, tv, rt, ev.apps(vspine).lams(vvs, vrt), eb.apps(spine))
            .lams(vs, rt),
          tb
        )
      case S.LetRec(_, ty, v, b) =>
        val x = fresh()
        val tv = goTDef(ty)
        val (ev, _) = go(v)(ref, (x, tv) :: ctx)
        val (eb, tb) = go(b)(ref, (x, tv) :: ctx)
        val (vs, rt, spine) = eta(tb)
        (LetRec(x, tv, rt, ev, eb.apps(spine)).lams(vs, rt), tb)
      case S.Match(s, t, c, ps, b, o) =>
        val x = fresh()
        val dt = goTy(t)
        val TCon(dx) = dt: @unchecked
        val (es, _) = go(s)
        val vx = Var(x, TDef(dt))
        val eb =
          (0 until ps.size).zip(ps).foldLeft(go(b)._1) { case (v, (i, t)) =>
            App(v, Field(dx, c, vx, goTy(t), i))
          }
        val (eo, to) = go(o)
        val (vs, rt, spine) = eta(to)
        (
          Match(dx, es, rt, c, x, eb.apps(spine), eo.apps(spine)).lams(vs, rt),
          to
        )

      case S.Splice(tm)  => impossible()
      case S.Prim0(name) => impossible()

  private inline def fresh()(implicit ref: Ref[LName]): LName =
    ref.updateGetOld(_ + 1)

  private def eta(ty: TDef)(implicit
      ref: Ref[LName]
  ): (List[(LName, Ty)], Ty, List[Tm]) =
    val ps = ty.ps
    val vs = ps.foldLeft(List.empty[(LName, Ty)])((vs, ty) =>
      vs ++ List((fresh(), ty))
    )
    val spine = vs.map((x, t) => Var(x, TDef(t)))
    (vs, ty.rt, spine)

  // monomorphization
  type DatatypeCons = List[(Name, List[(Bind, Ty)])]
  type Datatype = (Name, DataKind, DatatypeCons)
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
    case VTCon(dx, ps)                                     => TCon(mono(dx, ps))
    case VPrim1(x)                                         => TPrim(x)
    case VRigid(HPrim(Name("Array")), SApp(SId, ty, Expl)) => TArray(goVTy(ty))
    case _                                                 => impossible()

  private def genName(dx: Name, ps: List[Ty]): Name =
    if ps.isEmpty then dx
    else
      val gps = ps.map(genName).mkString("_")
      Name(s"${dx}_$gps")
  private def genName(t: Ty): Name = t match
    case TCon(dx)   => dx
    case TPrim(x)   => x
    case TArray(ty) => Name(s"Array_${genName(ty)}")

  private def mono(dx: Name, ps: List[VTy]): Name =
    val mps = ps.map(goVTy)
    monoMap.get((dx, mps)) match
      case Some(x) => x
      case None =>
        val x = genName(dx, mps)
        monoMap += (dx, mps) -> x
        monoData += ((x, getGlobalData0(dx).kind, monoCons(dx, ps)))
        x

  private def monoCons(dx: Name, ps: List[VTy]): DatatypeCons =
    val env = ps.foldLeft(EEmpty)(E1.apply)
    getGlobalData0(dx).cons.map { cx =>
      val ps = getGlobalCon0(cx).params.map((x, t) => (x, goTy(t, env)))
      (cx, ps)
    }

  def monomorphizedDatatypes: List[Datatype] = monoData.toList

  def monomorphizedDatatype(dx: Name): Datatype =
    monomorphizedDatatypes.find(_._1 == dx).get
