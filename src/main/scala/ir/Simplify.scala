package ir

import Syntax.*
import common.Ref

object Simplify:
  def simplify(t: Tm)(implicit ref: Ref[LName]): Tm = go(t)

  // TODO: lambda lifting, eta expansion
  // TODO: definition lifting
  // TODO: join points, contification, loopification
  private def go(t: Tm)(implicit ref: Ref[LName]): Tm = t match
    case Var(_, _)    => t
    case Global(_, _) => t
    case Impossible   => t

    case Let(x, ty, bty, v, b0) =>
      go(v) match
        case Let(y, ty2, bty2, v2, b2) =>
          go(Let(y, ty2, bty, v2, Let(x, ty, bty, b2, b0)))
        case LetRec(y, ty2, bty2, v2, b2) =>
          go(LetRec(y, ty2, bty, v2, Let(x, ty, bty, b2, b0)))
        case v =>
          val b = go(b0)
          (v, b) match
            case (Impossible, _) => Impossible
            case (_, Impossible) => Impossible
            case _ =>
              val count = b.free.count(_ == x)
              if count == 0 then b
              else if count == 1 then go(b.subst(x, v))
              else if isSmall(v) then go(b.subst(x, v))
              else Let(x, ty, bty, v, b)

    case LetRec(x, ty, bty, v, b0) =>
      go(v) match
        case Let(y, ty2, bty2, v2, b2) =>
          go(Let(y, ty2, bty, v2, LetRec(x, ty, bty, b2, b0)))
        case LetRec(y, ty2, bty2, v2, b2) =>
          go(LetRec(y, ty2, bty, v2, LetRec(x, ty, bty, b2, b0)))
        case v =>
          val b = go(b0)
          (v, b) match
            case (Impossible, _) => Impossible
            case (_, Impossible) => Impossible
            case _ =>
              val count = b.free.count(_ == x)
              if count == 0 then b
              else LetRec(x, ty, bty, v, b)

    case Lam(x, ty, bty, b) => Lam(x, ty, bty, go(b))

    case App(f, a) =>
      go(f) match
        case Impossible             => Impossible
        case Lam(x, t, bt, b)       => go(Let(x, TDef(t), bt, a, b))
        case Let(x, t, bt, v, b)    => go(Let(x, t, bt.tail, v, App(b, a)))
        case LetRec(x, t, bt, v, b) => go(LetRec(x, t, bt.tail, v, App(b, a)))
        case Match(s, t, bt, c, x, b, o) =>
          val y = fresh()
          val vt = TDef(bt.head)
          val vy = Var(y, vt)
          go(
            Let(
              y,
              vt,
              bt.tail,
              a,
              Match(s, t, bt.tail, c, x, App(b, vy), App(o, vy))
            )
          )
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
          go(o) match
            case Impossible => go(Let(x, TDef(t), bt, s, b))
            case o          => Match(s, t, bt, c, x, go(b), o)

    case Field(v, ty, ix) =>
      go(v) match
        case Impossible          => Impossible
        case Con(_, args)        => args(ix)
        case Let(x, t, bt, v, b) => go(Let(x, t, TDef(ty), v, Field(b, ty, ix)))
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
