package ir

import common.Common.*
import common.Ref

object Syntax:
  type LName = Int

  enum Ty:
    case TCon(name: Name)

    override def toString: String = this match
      case TCon(name) => s"$name"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = ps match
      case Nil => s"$rt"
      case ps  => s"${ps.mkString("(", ", ", ")")} -> $rt"
    def tail: TDef = TDef(ps.tail, rt)
    def ty: Ty = ps match
      case Nil => rt
      case _   => impossible()
    def head: Ty = ps match
      case Nil     => impossible()
      case hd :: _ => hd
  object TDef:
    def apply(rt: Ty): TDef = TDef(Nil, rt)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.rt)

  enum Tm:
    case Var(name: LName, ty: TDef)
    case Global(name: Name, ty: TDef)
    case Let(name: LName, ty: TDef, bty: TDef, value: Tm, body: Tm)
    case LetRec(name: LName, ty: TDef, bty: TDef, value: Tm, body: Tm)
    case Lam(name: LName, ty: Ty, bty: TDef, body: Tm)
    case App(fn: Tm, arg: Tm)
    case Con(name: Name, args: List[Tm])
    case Match(
        scrut: Tm,
        ty: Ty,
        bty: TDef,
        con: Name,
        name: LName,
        body: Tm,
        other: Tm
    )
    case Impossible
    case Field(value: Tm, rt: Ty, ix: Int)

    override def toString: String = this match
      case Var(x, _)              => s"'$x"
      case Global(x, _)           => s"$x"
      case Let(x, ty, _, v, b)    => s"(let '$x : $ty := $v; $b)"
      case LetRec(x, ty, _, v, b) => s"(let rec '$x : $ty := $v; $b)"
      case Lam(x, ty, _, b)       => s"(\\('$x : $ty) => $b)"
      case App(fn, arg)           => s"($fn $arg)"
      case Con(x, Nil)            => s"$x"
      case Con(x, as)             => s"($x ${as.mkString(" ")})"
      case Match(scrut, _, _, c, x, b, e) =>
        s"(match $scrut | $c as '$x => $b | _ => $e)"
      case Impossible          => "impossible"
      case Field(value, _, ix) => s"(#$ix $value)"

    def subst(x: LName, v: Tm): Tm = subst(Map(x -> v))
    def subst(ss: Map[LName, Tm]): Tm = this match
      case Var(x, _)             => ss.get(x).getOrElse(this)
      case Global(x, _)          => this
      case Impossible            => this
      case Field(value, ty, ix)  => Field(value.subst(ss), ty, ix)
      case App(fn, arg)          => App(fn.subst(ss), arg.subst(ss))
      case Con(x, args)          => Con(x, args.map(_.subst(ss)))
      case Let(x, ty, bty, v, b) => Let(x, ty, bty, v.subst(ss), b.subst(ss))
      case LetRec(x, ty, bty, v, b) =>
        LetRec(x, ty, bty, v.subst(ss), b.subst(ss))
      case Lam(x, ty, bty, body) => Lam(x, ty, bty, body.subst(ss))
      case Match(s, t, bty, c, x, b, o) =>
        Match(s.subst(ss), t, bty, c, x, b.subst(ss), o.subst(ss))

    def free: List[LName] = this match
      case Var(x, _)           => List(x)
      case Global(x, _)        => Nil
      case Con(_, args)        => args.flatMap(_.free)
      case App(f, a)           => f.free ++ a.free
      case Impossible          => Nil
      case Field(v, _, ix)     => v.free
      case Let(x, ty, _, v, b) => v.free ++ b.free.filterNot(_ == x)
      case LetRec(x, ty, _, v, b) =>
        v.free.filterNot(_ == x) ++ b.free.filterNot(_ == x)
      case Lam(x, ty, _, b) => b.free.filterNot(_ == x)
      case Match(s, _, _, _, x, b, o) =>
        s.free ++ b.free.filterNot(_ == x) ++ o.free
  export Tm.*
