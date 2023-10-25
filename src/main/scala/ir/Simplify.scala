package ir

import common.Common.*
import Syntax.*
import common.Ref

import scala.collection.mutable

object Simplify:
  def simplify(x: Name, t: Tm, ty: TDef)(implicit
      ref: Ref[LName]
  ): List[(Name, TDef, Tm)] =
    val extraDefs = mutable.ArrayBuffer.empty[(Name, TDef, Tm)]
    var uniq = 0
    implicit val gendef: GenDef = k =>
      val dx = Name(s"${x.expose}$$$uniq")
      uniq += 1
      val ((ty, v), r) = k(dx)
      extraDefs += ((dx, ty, v))
      r
    val (vs, rt, spine) = eta(ty)
    val ev = go(t.apps(spine).lams(vs, rt))
    extraDefs.toList ++ List((x, ty, ev))

  private type GenDef = (Name => ((TDef, Tm), Tm)) => Tm

  // TODO: join points, contification, loopification
  // TODO: optimize by doing bottom-up eta-conversion
  private def go(t: Tm)(implicit ref: Ref[LName], gendef: GenDef): Tm =
    t match
      case Var(_, _)    => t
      case Global(_, _) => t
      case Impossible   => t

      case Let(x, ty, bty, v0, b0) =>
        val (vvs, rt, spine) = eta(ty)
        go(v0.apps(spine).lams(vvs, rt)) match
          case Let(y, ty2, bty2, v2, b2) =>
            go(Let(y, ty2, bty, v2, Let(x, ty, bty, b2, b0)))
          case LetRec(y, ty2, bty2, v2, b2) =>
            go(LetRec(y, ty2, bty, v2, Let(x, ty, bty, b2, b0)))
          case v =>
            val (vs, rt, spine) = eta(bty)
            val b = go(b0.apps(spine))
            (v0, v, b) match
              case (Impossible, _, _) => Impossible
              case (_, Impossible, _) => Impossible
              case (_, _, Impossible) => Impossible
              case _ =>
                val count = b.free.count((y, _) => x == y)
                if count == 0 then b.lams(vs, rt)
                else if count == 1 || isSmall(v) then
                  go(b.subst(x, v)).lams(vs, rt)
                else if isSmall(v0) then go(b.subst(x, v0)).lams(vs, rt)
                else if ty.isFunction then
                  val ps =
                    v.free.distinctBy((x, _) => x).map((x, t) => (x, t.ty))
                  val nty = TDef(ps.map(_._2), ty)
                  val nv = v.lams(ps, ty)
                  gendef { vx =>
                    val gl =
                      Global(vx, nty).apps(ps.map((x, t) => Var(x, TDef(t))))
                    val r = go(b.subst(x, gl)).lams(vs, rt)
                    ((nty, nv), r)
                  }
                else Let(x, ty, bty, v, b).lams(vs, rt)

      case LetRec(x, ty, bty, v0, b0) =>
        val (vs, rt, spine) = eta(ty)
        go(v0.apps(spine).lams(vs, rt)) match
          case Let(y, ty2, bty2, v2, b2) =>
            go(Let(y, ty2, bty, v2, LetRec(x, ty, bty, b2, b0)))
          case LetRec(y, ty2, bty2, v2, b2) =>
            go(LetRec(y, ty2, bty, v2, LetRec(x, ty, bty, b2, b0)))
          case v =>
            val (vs, rt, spine) = eta(bty)
            val b = go(b0.apps(spine))
            (v0, v, b) match
              case (Impossible, _, _) => Impossible
              case (_, Impossible, _) => Impossible
              case (_, _, Impossible) => Impossible
              case _ =>
                val count = b.free.count((y, _) => x == y)
                if count == 0 then b.lams(vs, rt)
                else
                  val ps =
                    v.free
                      .filterNot((y, _) => x == y)
                      .distinctBy((x, _) => x)
                      .map((x, t) => (x, t.ty))
                  val nty = TDef(ps.map(_._2), ty)
                  gendef { vx =>
                    val gx = Global(vx, nty)
                    val nv = go(v.subst(x, gx)).lams(ps, ty)
                    val gl = gx.apps(ps.map((x, t) => Var(x, TDef(t))))
                    val r = go(b.subst(x, gl)).lams(vs, rt)
                    ((nty, nv), r)
                  }

      case Lam(x, ty, bty, b) => Lam(x, ty, bty, go(b))

      case App(f, a) =>
        go(f) match
          case Impossible       => Impossible
          case Lam(x, t, bt, b) => go(Let(x, TDef(t), bt, a, b))
          case f =>
            go(a) match
              case Impossible => Impossible
              case a          => App(f, a)

      case Con(x, args) => Con(x, args.map(go))

      case Match(s, t, bt, c, x, b, o) =>
        go(s) match
          case Impossible                => Impossible
          case s @ Con(c2, _) if c == c2 => go(b.subst(x, s))
          case Con(_, _)                 => go(o)
          case Let(y, t2, bt2, v, b2) =>
            go(Let(y, t2, bt, v, Match(b2, t, bt, c, x, b, o)))
          case Match(s2, t2, bt2, c2, x2, b2, o2) =>
            val tf = TDef(t, bt)
            val f = fresh()
            val vf = Var(f, tf)
            val y = fresh()
            go(
              Let(
                f,
                TDef(t, bt),
                bt,
                Lam(y, t, bt, Match(Var(y, TDef(t)), t, bt, c, x, b, o)),
                Match(s2, t2, bt, c2, x2, App(vf, b2), App(vf, o2))
              )
            )
          case s =>
            val (vs, rt, spine) = eta(bt)
            val eb = go(b.apps(spine))
            go(o.apps(spine)) match
              case Impossible => go(Let(x, TDef(t), rt, s, eb)).lams(vs, rt)
              case o =>
                Match(s, t, rt, c, x, eb, o).lams(vs, rt)

      case Field(v, ty, ix) =>
        go(v) match
          case Impossible   => Impossible
          case Con(_, args) => args(ix)
          case Let(x, t, bt, v, b) =>
            go(Let(x, t, TDef(ty), v, Field(b, ty, ix)))
          case LetRec(x, t, bt, v, b) =>
            go(LetRec(x, t, TDef(ty), v, Field(b, ty, ix)))
          case Match(s, t, bt, c, x, b, o) =>
            go(Match(s, t, TDef(ty), c, x, Field(b, ty, ix), Field(o, ty, ix)))
          case v => Field(v, ty, ix)

  private def isSmall(t: Tm): Boolean = t match
    case Var(_, _)    => true
    case Global(_, _) => true
    case Con(_, Nil)  => true
    case Impossible   => true
    case _            => false

  private inline def fresh()(implicit ref: Ref[LName]): LName =
    ref.updateGetOld(_ + 1)

  private def eta(ty: TDef)(implicit
      ref: Ref[LName]
  ): (List[(LName, Ty)], TDef, List[Tm]) =
    val ps = ty.ps
    val vs = ps.foldLeft(List.empty[(LName, Ty)])((vs, ty) =>
      vs ++ List((fresh(), ty))
    )
    val spine = vs.map((x, t) => Var(x, TDef(t)))
    (vs, ty.returnType, spine)
