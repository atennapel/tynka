package ir

import common.Common.*
import common.Ref
import core.Syntax as S
import Syntax.*
import core.Globals.*
import core.Value.*
import core.Evaluation.{stage, stageUnder, forceAll1, eval1}

import scala.collection.mutable

object Monomorphize:
  // t should be staged
  // t will be monomorphized and eta-expanded
  def monomorphize(t: S.Tm0)(implicit ref: Ref[LName]): Tm =
    val (tm, ty) = go(t)(ref, Nil, EEmpty)
    val (vs, rt, spine) = eta(ty)
    tm.apps(spine).lams(vs, rt)

  def monomorphize(t: S.Ty): TDef = goTDef(t)

  type Ctx = List[(LName, TDef)]

  private def go(
      t: S.Tm0
  )(implicit ref: Ref[LName], ctx: Ctx, env: Env): (Tm, TDef) =
    inline def go1(t: S.Tm1) = go(stageUnder(S.Splice(t), env))._1
    inline def go1Under(x: LName, ty: TDef, t: S.Tm1) =
      go(stageUnder(S.Splice(t), nextEnv))(ref, (x, ty) :: ctx, nextEnv)._1
    inline def nextEnv = E0(env, VVar0(mkLvl(env.size)))
    t match
      case S.IntLit(v)    => (IntLit(v), TDef(TPrim(Name("Int"))))
      case S.StringLit(v) => (StringLit(v), TDef(TClass("java.lang.String")))
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
      case S.Wk00(tm) => go(tm)(ref, ctx.tail, env.tail)

      case S.Lam0(_, ty, b) =>
        val x = fresh()
        val ta = goTy(ty)
        val (eb, bty) =
          go(b)(ref, (x, TDef(ta)) :: ctx, nextEnv)
        val (vs, rt, spine) = eta(bty)
        (eb.apps(spine).lams((x, ta) :: vs, rt), TDef(ta, bty))
      case S.Let0(_, ty, v, b) =>
        val x = fresh()
        val tv = goTDef(ty)
        val (vvs, vrt, vspine) = eta(tv)
        val (ev, _) = go(v)
        val (eb, tb) = go(b)(ref, (x, tv) :: ctx, nextEnv)
        val (vs, rt, spine) = eta(tb)
        (
          Let(false, x, tv, rt, ev.apps(vspine).lams(vvs, vrt), eb.apps(spine))
            .lams(vs, rt),
          tb
        )
      case S.LetRec(_, ty, v, b) =>
        val x = fresh()
        val tv = goTDef(ty)
        val (vvs, vrt, vspine) = eta(tv)
        val (ev, _) = go(v)(ref, (x, tv) :: ctx, nextEnv)
        val (eb, tb) = go(b)(ref, (x, tv) :: ctx, nextEnv)
        val (vs, rt, spine) = eta(tb)
        (
          LetRec(
            x,
            tv,
            rt,
            ev.apps(vspine).lams(vvs, vrt),
            eb.apps(spine)
          )
            .lams(vs, rt),
          tb
        )
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
          Match(dx, es, rt, c, x, eb.apps(spine), eo.apps(spine))
            .lams(vs, rt),
          to
        )

      case S.Foreign(io, ty, code, args) =>
        val rt = goTy(ty)
        val eargs = args.map { t =>
          val (et, ty) = go(t)
          (et, ty.ty)
        }
        val inner = Foreign(rt, goLabel(code), eargs)
        if io then
          val x = fresh()
          (
            Lam(List((x, TDummy)), rt, inner),
            TDef(List(TDummy), rt)
          )
        else (inner, TDef(rt))

      case S.Splice(tm) =>
        def flatten(tm: S.Tm1): (String, List[S.Tm1]) = tm match
          case S.App1(hd, arg, _) =>
            val (x, args) = flatten(hd)
            (x, args ++ List(arg))
          case S.Prim1(x) => (x.expose, Nil)
          case _          => impossible()
        flatten(tm) match
          case ("returnIO", List(t, v)) =>
            val x = fresh()
            val rt = goTy(t)
            val ev = go1(v)
            (Lam(List((x, TDummy)), rt, ev), TDef(TDummy, rt))
          case ("unsafePerformIO", List(t, v)) =>
            (App(go1(v), DummyValue), TDef(goTy(t)))
          case ("bindIO", List(a, b, c, k)) =>
            // bindIO {a} {b} c k ~> \(w : Dummy) => let noinline r = c w; k r w
            val x = fresh()
            val t1 = goTy(a)
            val t2 = goTy(b)
            val ec = go1(c)
            val ek =
              go(
                S.Lam0(
                  DoBind(Name("x")),
                  a,
                  stageUnder(
                    S.Splice(S.App1(S.Wk01(k), S.Quote(S.Var0(ix0)), Expl)),
                    nextEnv
                  )
                )
              )._1
            val r = fresh()
            val vx = Var(x, TDef(TDummy))
            (
              Lam(
                List((x, TDummy)),
                t2,
                Let(
                  true,
                  r,
                  TDef(t1),
                  t2,
                  App(ec, vx),
                  App(App(ek, Var(r, TDef(t1))), vx)
                )
              ),
              TDef(TDummy, t2)
            )
          case _ => impossible()
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
    case VFun(_, pty, _, rty) => TDef(goVTy(pty), goVTDef(rty))
    case VRigid(HPrim(Name("IO")), SApp(SApp(SId, _, Impl), ty, Expl)) =>
      TDef(TDummy, goVTy(ty))
    case t => TDef(goVTy(t))

  private inline def goTy(t: S.Ty, env: Env = EEmpty): Ty = goVTy(eval1(t)(env))
  private def goVTy(t: VTy): Ty = forceAll1(t) match
    case VTConApp(dx, ps)           => TCon(mono(dx, ps.map(_._1)))
    case VPrim1(x @ Name("Byte"))   => TPrim(x)
    case VPrim1(x @ Name("Short"))  => TPrim(x)
    case VPrim1(x @ Name("Int"))    => TPrim(x)
    case VPrim1(x @ Name("Long"))   => TPrim(x)
    case VPrim1(x @ Name("Float"))  => TPrim(x)
    case VPrim1(x @ Name("Double")) => TPrim(x)
    case VPrim1(x @ Name("Char"))   => TPrim(x)
    case VRigid(HPrim(Name("Array")), SApp(SId, ty, Expl)) => TArray(goVTy(ty))
    case VRigid(HPrim(Name("Class")), SApp(SId, l, Expl)) => TClass(goVLabel(l))
    case _                                                => TDummy

  private def goLabel(l: S.Tm1): String = goVLabel(eval1(l)(EEmpty))
  private def goVLabel(l: Val1): String =
    forceAll1(l) match
      case VLabelLit(x) => x
      case _            => impossible()

  private def genName(dx: Name, ps: List[Ty]): Name =
    if ps.isEmpty then dx
    else
      val gps = ps.filterNot(_ == TDummy).map(genName).mkString("_")
      Name(s"${dx}_$gps")
  private def genName(t: Ty): Name = t match
    case TCon(dx)   => dx
    case TPrim(x)   => x
    case TArray(ty) => Name(s"Array$$${genName(ty)}")
    case TClass(x)  => Name(x.replace(".", "$"))
    case TDummy     => impossible()

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
      val ps = getGlobalCon0(cx).params.map((x, _, t) => (x, goTy(t, env)))
      (cx, ps)
    }

  def monomorphizedDatatypes: List[Datatype] = monoData.toList

  def monomorphizedDatatype(dx: Name): Datatype =
    monomorphizedDatatypes.find(_._1 == dx).get
