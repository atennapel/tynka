package ir

import common.Common.*
import Syntax.*
import common.Ref

import scala.collection.mutable

object Simplify:
  def simplify(x: Name, t: Tm, ty: TDef)(implicit
      ref: Ref[LName]
  ): List[(Boolean, Name, TDef, Tm)] =
    val extraDefs = mutable.ArrayBuffer.empty[(Name, TDef, Tm)]
    var uniq = 0
    implicit val gendef: GenDef[Tm] = k =>
      val dx = Name(s"${x.expose}$$$uniq")
      uniq += 1
      val ((ty, v), r) = k(dx)
      extraDefs += ((dx, ty, v))
      r
    val ev = go(t) // do not inline
    val genDefs = extraDefs.toList.map((x, t, v) => (true, x, t, v))
    genDefs ++ List((false, x, ty, ev))

  private type GenDef[R] = (Name => ((TDef, Tm), R)) => R

  private def go(t: Tm)(implicit ref: Ref[LName], gendef: GenDef[Tm]): Tm =
    t match
      case Var(_, _)        => t
      case Global(_, _)     => t
      case Impossible(_)    => t
      case Jump(x, t, args) => Jump(x, t, args.map(go))

      case l @ Let(x, ty, bty, v0, b) =>
        go(v0) match
          case Let(y, ty2, bty2, v2, b2) =>
            go(Let(y, ty2, bty, v2, Let(x, ty, bty, b2, b)))
          case LetRec(y, ty2, bty2, v2, b2) =>
            go(LetRec(y, ty2, bty, v2, Let(x, ty, bty, b2, b)))
          case Join(y, ps, bty2, v2, b2) =>
            go(Join(y, ps, bty, v2, Let(x, ty, bty, b2, b)))
          case JoinRec(y, ps, bty2, v2, b2) =>
            go(JoinRec(y, ps, bty, v2, Let(x, ty, bty, b2, b)))
          case v =>
            (v0, v, go(b)) match
              case (Impossible(_), _, _) => Impossible(TDef(bty))
              case (_, Impossible(_), _) => Impossible(TDef(bty))
              case (_, _, Impossible(_)) => Impossible(TDef(bty))
              case (_, v, b) =>
                val count = b.free.count((y, _) => x == y)
                if count == 0 then b
                else if count == 1 || isSmall(v) then go(b.subst(x, v))
                else if isSmall(v0) then go(b.subst(x, v0))
                else if tailPos(x, v, b) then
                  v.flattenLams match
                    case (None, v) =>
                      val nb = b.subst(x, Jump(x, ty, Nil))
                      go(Join(x, Nil, ty.ty, v, nb))
                    case (Some((ps, rt)), v) =>
                      val (jps, rt, spine) = eta(ty)
                      val j = Jump(x, ty, spine).lams(jps, rt)
                      val nb = b.subst(x, j)
                      go(Join(x, ps, rt, v, nb))
                else if ty.isFunction then
                  val ps =
                    v.free.distinctBy((x, _) => x).map((x, t) => (x, t.ty))
                  val nty = TDef(ps.map(_._2), ty)
                  val Lam(vps, vrt, vb) = v: @unchecked
                  val nv = vb.lams(ps ++ vps, vrt)
                  gendef { vx =>
                    val gl =
                      Global(vx, nty).apps(ps.map((x, t) => Var(x, TDef(t))))
                    val r = go(b.subst(x, gl))
                    ((nty, nv), r)
                  }
                else Let(x, ty, bty, v, b)

      case LetRec(x, ty, bty, v0, b) =>
        go(v0) match
          case Let(y, ty2, bty2, v2, b2) =>
            go(Let(y, ty2, bty, v2, LetRec(x, ty, bty, b2, b)))
          case LetRec(y, ty2, bty2, v2, b2) =>
            go(LetRec(y, ty2, bty, v2, LetRec(x, ty, bty, b2, b)))
          case Join(y, ps, bty2, v2, b2) =>
            go(Join(y, ps, bty, v2, LetRec(x, ty, bty, b2, b)))
          case JoinRec(y, ps, bty2, v2, b2) =>
            go(JoinRec(y, ps, bty, v2, LetRec(x, ty, bty, b2, b)))
          case v =>
            (v0, v, go(b)) match
              case (Impossible(_), _, _) => Impossible(TDef(bty))
              case (_, Impossible(_), _) => Impossible(TDef(bty))
              case (_, _, Impossible(_)) => Impossible(TDef(bty))
              case (_, v, b) =>
                val Lam(ps, rt, vb) = v: @unchecked
                val count = b.free.count((y, _) => x == y)
                if count == 0 then b
                else if tailPos(x, v, vb) then
                  if tailPos(x, v, b) then
                    val (vs, rt1, spine) = eta(ty)
                    val (vs2, rt2, spine2) = eta(ty)
                    val vv = vb.subst(x, Jump(x, ty, spine).lams(vs, rt1))
                    val nb = b.subst(x, Jump(x, ty, spine2).lams(vs2, rt2))
                    go(JoinRec(x, ps, rt, vv, nb))
                  else
                    val (vs, rt1, spine) = eta(ty)
                    val vv = vb.subst(x, Jump(x, ty, spine).lams(vs, rt1))
                    val (vs2, rt2, spine2) = eta(ty)
                    val nb = Jump(x, ty, spine2)
                    val db = go(JoinRec(x, ps, rt, vv, nb)).lams(vs2, rt2)
                    val ps2 =
                      db.free
                        .filterNot((y, _) => x == y)
                        .distinctBy((x, _) => x)
                        .map((x, t) => (x, t.ty))
                    val nty = TDef(ps2.map(_._2), ty)
                    gendef { vx =>
                      val gl =
                        Global(vx, nty).apps(ps.map((x, t) => Var(x, TDef(t))))
                      val r = go(b.subst(x, gl))
                      ((ty, db), r)
                    }
                else
                  val ps =
                    v.free
                      .filterNot((y, _) => x == y)
                      .distinctBy((x, _) => x)
                      .map((x, t) => (x, t.ty))
                  val nty = TDef(ps.map(_._2), ty)
                  val Lam(vps, vrt, vb) = v: @unchecked
                  gendef { vx =>
                    val gl =
                      Global(vx, nty).apps(ps.map((x, t) => Var(x, TDef(t))))
                    val nv = go(vb.subst(x, gl)).lams(ps ++ vps, vrt)
                    val r = go(b.subst(x, gl))
                    ((nty, nv), r)
                  }

      case Join(x, ps, bty, v0, b0) =>
        val v = go(v0)
        val b = go(b0)
        val count = b.free.count((y, _) => x == y)
        if count == 0 then b
        else if count == 1 || isSmall(v) then go(b.subst(x, v))
        else if isSmall(v0) then go(b.subst(x, v0))
        else Join(x, ps, bty, v, b)

      case JoinRec(x, ps, bty, v0, b0) =>
        val v = go(v0)
        val b = go(b0)
        val count = b.free.count((y, _) => x == y)
        if count == 0 then b
        else JoinRec(x, ps, bty, v, b)

      case Lam(ps, rt, b) => Lam(ps, rt, go(b))

      case app @ App(_, _) =>
        val (f, args) = app.flattenApps
        go(f) match
          case Impossible(ty)    => Impossible(ty.tail)
          case j @ Jump(_, _, _) => j
          case l @ Lam(ps, bt, b) =>
            if args.size != ps.size then impossible()
            val lets = ps.zip(args).foldRight(b) { case (((x, t), a), b) =>
              Let(x, TDef(t), bt, a, b)
            }
            go(lets)
          case f => f.apps(args.map(go))

      case Con(x, t, args) => Con(x, t, args.map(go))

      case m @ Match(dx, s, bt, c, x, b, o) =>
        go(s) match
          case Impossible(ty) => Impossible(TDef(bt))
          case s @ Con(_, c2, _) if c == c2 =>
            go(Let(x, TDef(TCon(dx)), bt, s, b))
          case Con(_, _, _)      => go(o)
          case j @ Jump(_, _, _) => j
          case Let(y, t2, bt2, v, b2) =>
            go(Let(y, t2, bt, v, Match(dx, b2, bt, c, x, b, o)))
          case LetRec(y, t2, bt2, v, b2) =>
            go(LetRec(y, t2, bt, v, Match(dx, b2, bt, c, x, b, o)))
          case Join(y, ps, t2, v, b2) =>
            go(
              Join(
                y,
                ps,
                bt,
                Match(dx, v, bt, c, x, b, o),
                Match(dx, b2, bt, c, x, b, o)
              )
            )
          case JoinRec(y, ps, t2, v, b2) =>
            go(
              JoinRec(
                y,
                ps,
                bt,
                Match(dx, v, bt, c, x, b, o),
                Match(dx, b2, bt, c, x, b, o)
              )
            )
          case Match(dx2, s2, bt2, c2, x2, b2, o2) =>
            val f = fresh()
            val y = fresh()
            val t = TCon(dx)
            inline def vf(a: Tm) = Jump(f, TDef(t, bt), List(a))
            go(
              Join(
                f,
                List((y, t)),
                bt,
                Match(dx, Var(y, TDef(t)), bt, c, x, b, o),
                Match(dx2, s2, bt, c2, x2, vf(b2), vf(o2))
              )
            )
          case s =>
            val eb = go(b)
            go(o) match
              // case Impossible(_) => go(Let(x, TDef(t), bt, s, eb))
              case o => Match(dx, s, bt, c, x, eb, o)

      case Field(dx, cx, v, ty, ix) =>
        go(v) match
          case Impossible(_)     => Impossible(TDef(ty))
          case Con(_, _, args)   => args(ix)
          case j @ Jump(_, _, _) => j
          case Let(x, t, bt, v, b) =>
            go(Let(x, t, ty, v, Field(dx, cx, b, ty, ix)))
          case LetRec(x, t, bt, v, b) =>
            go(LetRec(x, t, ty, v, Field(dx, cx, b, ty, ix)))
          case Join(x, ps, rt, v, b) =>
            go(
              Join(
                x,
                ps,
                ty,
                Field(dx, cx, v, ty, ix),
                Field(dx, cx, b, ty, ix)
              )
            )
          case JoinRec(x, ps, rt, v, b) =>
            go(
              JoinRec(
                x,
                ps,
                ty,
                Field(dx, cx, v, ty, ix),
                Field(dx, cx, b, ty, ix)
              )
            )
          case Match(s, t, bt, c, x, b, o) =>
            go(
              Match(
                s,
                t,
                ty,
                c,
                x,
                Field(dx, cx, b, ty, ix),
                Field(dx, cx, o, ty, ix)
              )
            )
          case v => Field(dx, cx, v, ty, ix)

      /*
      case ReturnIO(v) =>
        go(v) match
          case Impossible(ty)    => Impossible(ty.returnIO)
          case j @ Jump(_, _, _) => j
          case Let(x, t, bt, v2, b) =>
            go(Let(x, t, bt.returnIO, v2, ReturnIO(b)))
          case LetRec(x, t, bt, v2, b) =>
            go(LetRec(x, t, bt.returnIO, v2, ReturnIO(b)))
          case Join(x, ps, rt, v2, b) =>
            go(Join(x, ps, rt.returnIO, ReturnIO(v2), ReturnIO(b)))
          case JoinRec(x, ps, rt, v2, b) =>
            go(JoinRec(x, ps, rt.returnIO, ReturnIO(v2), ReturnIO(b)))
          case Match(s, t, bt, c, x, b, o) =>
            go(Match(s, t, bt.returnIO, c, x, ReturnIO(b), ReturnIO(o)))
          case v => ReturnIO(v)
      case BindIO(x, t1, t2, v, b) =>
        go(v) match
          case BindIO(y, t3, t4, v2, b2) =>
            go(BindIO(y, t3, t2, v2, BindIO(x, t4, t2, b2, b)))
          case ReturnIO(v) => go(Let(x, TDef(t1), TDef(t2).returnIO, v, b))
          case Let(y, t, bt, v2, b2) =>
            go(Let(y, t, TDef(t2).returnIO, v2, BindIO(x, t1, t2, b2, b)))
          case LetRec(y, t, bt, v2, b2) =>
            go(LetRec(y, t, TDef(t2).returnIO, v2, BindIO(x, t1, t2, b2, b)))
          // TODO: join and match
          case v => BindIO(x, t1, t2, v, go(b))
      case RunIO(c) =>
        go(c) match
          case Impossible(ty)    => Impossible(TDef(ty.runIO))
          case j @ Jump(_, _, _) => j
          case ReturnIO(v)       => v
          case Let(x, t, bt, v2, b) =>
            go(Let(x, t, bt.runIO, v2, RunIO(b)))
          case LetRec(x, t, bt, v2, b) =>
            go(LetRec(x, t, bt.runIO, v2, RunIO(b)))
          case Join(x, ps, rt, v2, b) =>
            go(Join(x, ps, rt.runIO, RunIO(v2), RunIO(b)))
          case JoinRec(x, ps, rt, v2, b) =>
            go(JoinRec(x, ps, rt.runIO, RunIO(v2), RunIO(b)))
          case Match(s, t, bt, c, x, b, o) =>
            go(Match(s, t, bt.runIO, c, x, RunIO(b), RunIO(o)))
          case c => RunIO(c)*/

      case t => println(s"add case: $t"); impossible() // TODO: remove

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

  private def isSmall(t: Tm): Boolean = t match
    case Var(_, _)      => true
    case Global(_, _)   => true
    case Con(_, _, Nil) => true
    case Impossible(_)  => true
    case ReturnIO(v)    => isSmall(v)
    case RunIO(v)       => isSmall(v)
    case _              => false

  private def arity(t: Tm): Int = t match
    case Lam(ps, _, _) => ps.size
    case _             => 0

  private def tailPos(x: LName, v: Tm, b: Tm): Boolean = tailPos(x, arity(v), b)
  private def tailPos(x: LName, arity: Int, b: Tm): Boolean =
    inline def notContains(t: Tm): Boolean = t.free.forall((y, _) => x != y)
    inline def notAnyContains(t: List[Tm]): Boolean =
      t.flatMap(_.free).forall((y, _) => x != y)
    inline def inTail(t: Tm): Boolean = tailPos(x, arity, t)
    b match
      case Var(y, _)                => x != y || arity == 0
      case Impossible(_)            => true
      case Field(_, _, value, _, _) => notContains(value)
      case Global(_, _)             => true
      case Jump(_, _, args)         => notAnyContains(args)
      case Con(_, _, args)          => notAnyContains(args)
      case Lam(_, bty, body)        => notContains(body)

      case ReturnIO(v) => inTail(v)
      case RunIO(c)    => inTail(c)

      case t @ App(_, _) =>
        val (f, args) = t.flattenApps
        f match
          case Var(y, ty) if x == y && args.size == arity =>
            notAnyContains(args)
          case tm => notAnyContains(tm :: args)

      case Let(_, _, _, v, b)     => notContains(v) && inTail(b)
      case LetRec(_, _, _, v, b)  => notContains(v) && inTail(b)
      case Join(_, _, _, v, b)    => inTail(v) && inTail(b)
      case JoinRec(_, _, _, v, b) => inTail(v) && inTail(b)
      case Match(_, s, _, _, _, b, o) =>
        notContains(s) && inTail(b) && inTail(o)
      case BindIO(_, _, _, v, b) => notContains(v) && inTail(b)
