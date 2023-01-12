package ir

import Syntax.*

import scala.annotation.tailrec

object Simplifier:
  private val LIMIT_MULTIPLIER = 10

  def simplify(ds: Defs): Defs = Defs(ds.toList.map(go))

  private def go(d: Def): Def = d match
    case DDef(x, t, v) =>
      DDef(x, t, go(v, LIMIT_MULTIPLIER * v.size)(Set.empty))
    case d => d

  @tailrec
  private def go(t: Expr, n: Int)(implicit scope: Set[Int]): Expr =
    if n > 0 then
      go(t) match
        case None     => t
        case Some(t2) => go(t2, n - 1)
    else t

  private def go(t: Expr)(implicit scope: Set[Int]): Option[Expr] = t match
    case Var(_, _)    => None
    case Global(_, _) => None

    case App(Let(x, t, v, b), a) if scope.contains(x.expose) =>
      val y = scope.max + 1
      val ny = Name(y)
      Some(Let(ny, t, v, App(b.subst(Map(x -> Var(ny, t)), scope + y), a)))
    case App(Let(x, t, v, b), a)   => Some(Let(x, t, v, App(b, a)))
    case App(Lam(x, t1, t2, b), a) => Some(Let(x, TDef(t1), a, b))
    case App(f, a)                 => go2(f, a).map(App.apply)

    case Lam(x, t1, t2, b) => go(b)(scope + x.expose).map(Lam(x, t1, t2, _))

    case Let(y0, t2, Let(x, t1, v1, v2), b) =>
      val nscope = scope + x.expose
      if nscope.contains(y0.expose) then
        val y = nscope.max + 1
        val ny = Name(y)
        Some(
          Let(
            x,
            t1,
            v1,
            Let(ny, t2, v2, b.subst(Map(y0 -> Var(ny, t2)), nscope + y))
          )
        )
      else Some(Let(x, t1, v1, Let(y0, t2, v2, b)))
    case Let(x, t, v, b) =>
      // TODO: lift lambdas out of let body
      val c = b.fvs.count((y, _) => x == y)
      if c == 0 then Some(b)
      else if c == 1 || isInlineable(v) then Some(b.subst(Map(x -> v), scope))
      else
        (go(v), go(b)(scope + x.expose)) match
          case (None, None)       => None
          case (Some(v), None)    => Some(Let(x, t, v, b))
          case (None, Some(b))    => Some(Let(x, t, v, b))
          case (Some(v), Some(b)) => Some(Let(x, t, v, b))

    case Fix(g, x, t1, t2, b, arg) =>
      go(arg) match
        case Some(arg) =>
          go(b)(scope + g.expose + x.expose) match
            case Some(b) => Some(Fix(g, x, t1, t2, b, arg))
            case None    => Some(Fix(g, x, t1, t2, b, arg))
        case None =>
          go(b)(scope + g.expose + x.expose).map(Fix(g, x, t1, t2, _, arg))

    case Pair(fst, snd)    => go2(fst, snd).map(Pair(_, _))
    case Fst(Pair(fst, _)) => Some(fst)
    case Snd(Pair(_, snd)) => Some(snd)
    case Fst(t)            => go(t).map(Fst.apply)
    case Snd(t)            => go(t).map(Snd.apply)

    case IntLit(n) => None
    case BinOp(op, a, b) =>
      binop(op, a, b) match
        case Some(t) => Some(t)
        case None    => go2(a, b).map(BinOp(op, _, _))

    case Absurd => None

    case Unit => None

    case BoolLit(_)                  => None
    case If(_, BoolLit(true), a, _)  => Some(a)
    case If(_, BoolLit(false), _, b) => Some(b)
    case If(TDef(ps, rt), c, a, b) if ps.nonEmpty =>
      val (vs, innerscope) =
        ps.foldLeft[(List[(Name, Ty)], Set[Int])]((Nil, scope)) {
          case ((vs, scope), ty) =>
            val x = fresh(scope)
            (vs ++ List((Name(x), ty)), scope + x)
        }
      val spine = vs.map((x, t) => Var(x, TDef(t)))
      val ea = a.apps(spine)
      val eb = b.apps(spine)
      Some(If(TDef(rt), c, ea, eb).lams(vs, TDef(rt)))
    case If(t, c, a, b) =>
      go(c) match
        case Some(c) =>
          go2(a, b) match
            case Some((a, b)) => Some(If(t, c, a, b))
            case None         => Some(If(t, c, a, b))
        case None => go2(a, b).map(If(t, c, _, _))

    case LNil(_)                             => None
    case LCons(t, hd, tl)                    => go2(hd, tl).map(LCons(t, _, _))
    case CaseList(_, _, LNil(_), n, _, _, _) => Some(n)
    case CaseList(_, _, LCons(t, hd, tl), _, xhd, xtl, c) =>
      Some(Let(xhd, TDef(t), hd, Let(xtl, TDef(TList(t)), tl, c)))
    case CaseList(et, TDef(ps, rt), s, nil, hd, tl, cons) if ps.nonEmpty =>
      val (vs, innerscope) =
        ps.foldLeft[(List[(Name, Ty)], Set[Int])](
          (Nil, scope + hd.expose + tl.expose)
        ) { case ((vs, scope), ty) =>
          val x = fresh(scope)
          (vs ++ List((Name(x), ty)), scope + x)
        }
      val spine = vs.map((x, t) => Var(x, TDef(t)))
      val enil = nil.apps(spine)
      val econs = cons.apps(spine)
      Some(CaseList(et, TDef(rt), s, enil, hd, tl, econs).lams(vs, TDef(rt)))
    case CaseList(t1, t2, l, n, hd, tl, c) =>
      go2(l, n) match
        case Some((l, n)) =>
          go(c)(scope + hd.expose + tl.expose) match
            case Some(c) => Some(CaseList(t1, t2, l, n, hd, tl, c))
            case None    => Some(CaseList(t1, t2, l, n, hd, tl, c))
        case None =>
          go(c)(scope + hd.expose + tl.expose)
            .map(CaseList(t1, t2, l, n, hd, tl, _))

  private def isInlineable(v: Expr): Boolean = v match
    case BoolLit(_)   => true
    case IntLit(_)    => true
    case Unit         => true
    case LNil(_)      => true
    case Global(_, _) => true
    case Var(_, _)    => true
    case _            => false

  private def binop(op: Op, a: Expr, b: Expr): Option[Expr] = (op, a, b) match
    case (BAdd, IntLit(a), IntLit(b)) => Some(IntLit(a + b))
    case (BAdd, IntLit(0), b)         => Some(b)
    case (BAdd, b, IntLit(0))         => Some(b)
    case (BMul, IntLit(a), IntLit(b)) => Some(IntLit(a * b))
    case (BMul, x, IntLit(1))         => Some(x)
    case (BMul, IntLit(1), x)         => Some(x)
    case (BMul, x, IntLit(0))         => Some(IntLit(0))
    case (BMul, IntLit(0), x)         => Some(IntLit(0))
    case (BSub, IntLit(a), IntLit(b)) => Some(IntLit(a - b))
    case (BSub, x, IntLit(0))         => Some(x)
    case (BDiv, IntLit(a), IntLit(b)) => Some(IntLit(a / b))
    case (BDiv, x, IntLit(1))         => Some(x)
    case (BMod, IntLit(a), IntLit(b)) => Some(IntLit(a % b))
    case (BEq, IntLit(a), IntLit(b)) =>
      Some(if a == b then BoolLit(true) else BoolLit(false))
    case (BNeq, IntLit(a), IntLit(b)) => Some(Expr.fromBool(a != b))
    case (BGt, IntLit(a), IntLit(b))  => Some(Expr.fromBool(a > b))
    case (BLt, IntLit(a), IntLit(b))  => Some(Expr.fromBool(a < b))
    case (BGeq, IntLit(a), IntLit(b)) => Some(Expr.fromBool(a >= b))
    case (BLeq, IntLit(a), IntLit(b)) => Some(Expr.fromBool(a <= b))
    case _                            => None

  private def go2(a: Expr, b: Expr)(implicit
      scope: Set[Int]
  ): Option[(Expr, Expr)] =
    (go(a), go(b)) match
      case (None, None)       => None
      case (Some(a), None)    => Some((a, b))
      case (None, Some(b))    => Some((a, b))
      case (Some(a), Some(b)) => Some((a, b))

  def orL[A](f: A => Option[A], l: List[A]): Option[List[A]] =
    val l1 = l.map(x => (x, f(x)))
    if l1.forall((_, o) => o.isEmpty) then None
    else Some(l1.map((x, o) => o.getOrElse(x)))

  private def fresh(implicit scope: Set[Int]): Int =
    if scope.isEmpty then 0 else scope.max + 1
