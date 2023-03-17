package ho

import Syntax.*

object Simplification:
  def simplify(d: Defs): Defs = Defs(d.toList.map(simplify))

  def simplify(d: Def): Def = d match
    case DDef(m, x, g, t, v) => DDef(m, x, g, t, go(v))

  private def go(v: Tm): Tm = v match
    case Var(x, _)       => v
    case Global(m, x, _) => v

    case IntLit(n) => v

    case App(f, a) =>
      go(f) match
        case Lam(x, t, rt, b) => go(Let(x, false, TDef(t), rt, a, b))
        case f                => App(f, go(a))
    case Lam(x, t, rt, b) => Lam(x, t, rt, go(b))
    case Let(x, noinline, t, bt, v0, b0) =>
      val v = go(v0)
      val b = go(b0)
      val usage = b.fvs.count((y, _) => x == y)
      if !noinline && usage == 0 then b
      else if !noinline && (usage == 1 || isInlinable(v)) then
        go(b.subst(Map(x -> v)))
      else Let(x, noinline, t, bt, v, b)

    case Fix(t1, t2, g, x, b, arg) => Fix(t1, t2, g, x, go(b), go(arg))

  private def isInlinable(v: Tm): Boolean = v match
    case Var(_, _)       => true
    case Global(_, _, _) => true
    case IntLit(_)       => true
    case _               => false
