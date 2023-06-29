package ir

import common.Common.impossible
import common.Ref
import Syntax.*
import jvmir.Syntax as J

import scala.collection.mutable

// TODO: tail-calls, proper name generation
object Compilation:
  def compile(ds: Defs): J.Defs = J.Defs(ds.toList.flatMap(go))

  private def go(d: Def): List[J.Def] =
    conv(d).map { case DDef(x, gen, t, v) =>
      v.flattenLams match
        case (None, v) => J.DDef(x, gen, go(t), Nil, go(v))
        case (Some((ps, bt)), v) =>
          J.DDef(x, gen, go(t), ps.map((x, t) => (x, go(t))), go(v))
    }

  private def dropLambdas(n: Int, t: Tm): Tm = (n, t) match
    case (0, t)               => t
    case (n, Lam(_, _, _, b)) => dropLambdas(n - 1, b)
    case _                    => impossible()

  private def conv(d: Def): List[Def] = d match
    case DDef(x, gen, t, v) =>
      val (ps, rt, b) = etaExpand(t, v)
      implicit val newDefs: NewDefs = mutable.ArrayBuffer.empty
      implicit val uniq: Ref[Int] = Ref(0)
      implicit val defname: GName = x
      val cb = conv(b).lams(ps, TDef(rt))
      newDefs.toList.flatMap(conv) ++ List(DDef(x, gen, t, cb))

  private def go(t: Tm): J.Tm =
    t match
      case Var(x, _) => J.Var(x)
      case Global(x, t) =>
        if t.ps.nonEmpty then impossible()
        J.Global(x, go(t.rt))

      case IntLit(n) => J.IntLit(n)

      case app @ App(_, _) =>
        val (f, as) = app.flattenApps
        f match
          case Global(x, t) => J.GlobalApp(x, go(t), false, as.map(go))
          case _            => impossible()

      case Let(x, t, rt, v, b) => J.Let(x, go(t.ty), go(v), go(b))

      case Lam(x, t, rt, b) => impossible()

  private def go(t: Ty): J.Ty = t match
    case TInt => J.TInt

  private def go(t: TDef): J.TDef = t match
    case TDef(ps, rt) => J.TDef(ps.map(go), go(rt))

  private def goTy(t: TDef): J.Ty = t match
    case TDef(Nil, rt) => go(rt)
    case _             => impossible()

  // simplify and lambdalift
  private type NewDefs = mutable.ArrayBuffer[Def]

  private def conv(
      tm: Tm
  )(implicit defs: NewDefs, uniq: Ref[Int], defname: GName): Tm = tm match
    case Var(x, t)    => tm
    case Global(x, t) => tm
    case IntLit(n)    => tm

    case App(f, a) =>
      conv(f) match
        case Lam(x, t, rt, b)    => conv(Let(x, TDef(t), rt, a, b))
        case Let(x, t, rt, v, b) => conv(Let(x, t, rt.tail, v, App(b, a)))
        case f                   => App(f, conv(a))

    case Lam(x, t, rt, b) => Lam(x, t, rt, conv(b))

    case Let(x, t, bt, v, b0) =>
      conv(v) match
        case Let(y, t2, bt2, v2, b2) =>
          conv(Let(y, t2, bt, v2, Let(x, t, bt, b2, b0)))
        case v =>
          val b = conv(b0)
          val c = b.fvs.count((y, _) => x == y)
          if c == 0 then b
          else if c == 1 || isSmall(v) then conv(b.subst(Map(x -> v)))
          else if t.ps.isEmpty then
            val (vs, spine) = eta(bt.params)
            Let(x, t, TDef(bt.rt), v, conv(b.apps(spine)))
              .lams(vs, TDef(bt.rt))
          else
            val (vs, spine) = eta(t.params)
            val fv = v.fvs.map((x, t) => (x, t.ty)).distinctBy((y, _) => y)
            val nps = fv ++ vs
            val args = nps.zipWithIndex.map { case ((x, _), ix) =>
              x -> ix
            }.toMap
            val gx = s"$defname$$${uniq.updateGetOld(_ + 1)}"
            defs += DDef(
              gx,
              true,
              TDef(fv.map(_._2), t),
              v.apps(spine).lams(nps, TDef(t.rt))
            )
            val gl = Global(gx, TDef(nps.map(_._2), t.rt))
              .apps(fv.map((x, t) => Var(x, TDef(t))))
            val (vs2, spine2) = eta(bt.params)
            conv(b.subst(Map(x -> gl)).apps(spine2).lams(vs2, TDef(bt.rt)))

  private def isSmall(v: Tm): Boolean = v match
    case Var(_, _)    => true
    case Global(_, _) => true
    case IntLit(_)    => true
    case _            => false

  private def etaExpand(t: TDef, v: Tm): (List[(LName, Ty)], Ty, Tm) =
    val (ps, b) = v.flattenLams
    val ps1 = ps.map((ps, _) => ps).getOrElse(Nil)
    val mps = eta(t, ps1, v.usedNames)
    val nps = ps1 ++ mps
    val nb = b.apps(mps.map((x, t) => Var(x, TDef(t))))
    (nps, t.rt, nb)

  private def eta(
      t: TDef,
      ps: List[(LName, Ty)],
      scope: Set[LName] = Set.empty
  ): List[(LName, Ty)] =
    (t, ps) match
      case (TDef(Nil, rt), Nil) => Nil
      case (TDef(t :: ts, rt), Nil) =>
        val y = if scope.isEmpty then 0 else scope.max + 1
        val rest = eta(TDef(ts, rt), Nil, scope + y)
        (y, t) :: rest
      case (TDef(t1 :: ts, rt), (x, t2) :: rest) if t1 == t2 =>
        eta(TDef(ts, rt), rest, scope + x)
      case _ => impossible()

  private def eta(ps: List[Ty])(implicit
      uniq: Ref[Int]
  ): (List[(LName, Ty)], List[Tm]) =
    val vs =
      ps.foldLeft[List[(LName, Ty)]](Nil) { case (vs, ty) =>
        val x = uniq.updateGetOld(_ + 1)
        vs ++ List((x, ty))
      }
    val spine = vs.map((x, t) => Var(x, TDef(t)))
    (vs, spine)
