package core

import common.Common.*
import scala.annotation.tailrec

object Syntax:
  enum Tm0:
    case Var0(ix: Ix)
    case Global0(name: Name)
    case Prim0(name: Name)
    case IntLit(value: Int)
    case StringLit(value: String)
    case Let0(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case LetRec(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case Lam0(name: Bind, ty: Ty, body: Tm0)
    case App0(fn: Tm0, arg: Tm0)
    case Con(name: Name, ty: Ty, args: List[Tm0])
    case Match(
        scrut: Tm0,
        ty: Ty,
        con: Name,
        params: List[Ty],
        body: Tm0,
        other: Tm0
    )
    case Impossible(ty: Ty)
    case Splice(tm: Tm1)
    case Foreign(io: Boolean, ty: Ty, code: Tm1, args: List[Tm0])
    case Wk10(tm: Tm0)
    case Wk00(tm: Tm0)

    override def toString: String = this match
      case Var0(ix)            => s"'$ix"
      case Global0(x)          => s"$x"
      case Prim0(x)            => s"$x"
      case IntLit(v)           => s"$v"
      case StringLit(v)        => s"\"$v\""
      case Let0(x, ty, v, b)   => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b) => s"(let rec $x : $ty := $v; $b)"
      case Lam0(x, ty, b)      => s"(\\($x : $ty) => $b)"
      case App0(fn, arg)       => s"($fn $arg)"
      case Con(x, _, Nil)      => s"$x"
      case Con(x, _, as)       => s"($x ${as.mkString(" ")})"
      case Match(scrut, t, c, _, b, e) =>
        s"(match ($scrut : $t) | $c => $b | _ => $e)"
      case Impossible(_) => "impossible"
      case Splice(tm)    => s"$$$tm"
      case Foreign(io, ty, code, Nil) =>
        s"(unsafeJVM${if io then "IO" else ""} $ty $code)"
      case Foreign(io, ty, code, args) =>
        s"(unsafeJVM${if io then "IO" else ""} $ty $code ${args.mkString(" ")})"
      case Wk10(tm) => s"$tm"
      case Wk00(tm) => s"$tm"

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm0): Tm0 = if n == 0 then t else go(n - 1, Wk00(t))
      go(n, this)
  export Tm0.*

  type Ty = Tm1
  type CV = Ty

  enum Tm1:
    case Var1(ix: Ix)
    case Global1(name: Name)
    case Prim1(name: Name)
    case TCon(name: Name)
    case LabelLit(value: String)
    case Let1(name: Name, ty: Ty, value: Tm1, body: Tm1)

    case U0(cv: Tm1)
    case U1

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam1(name: Bind, icit: Icit, ty: Ty, body: Tm1)
    case App1(fn: Tm1, arg: Tm1, icit: Icit)

    case Fun(boxity: Ty, pty: Ty, cv: CV, rty: Ty)
    case CV1
    case Comp
    case Lift(cv: CV, ty: Ty)

    case Quote(tm: Tm0)

    case Wk01(tm: Tm1)
    case Wk11(tm: Tm1)

    case Meta(id: MetaId)
    case MetaPi(meta: Boolean, ty: Ty, body: Ty)
    case MetaLam(meta: Boolean, body: Tm1)
    case MetaApp(fn: Tm1, arg: Either[Tm0, Tm1])
    case AppPruning(id: MetaId, pruning: Pruning)
    case PostponedCheck1(id: PostponedId)

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk01(t))
      go(n, this)

    def wk1N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk11(t))
      go(n, this)

    override def toString: String = this match
      case Var1(ix)             => s"'$ix"
      case Global1(x)           => s"$x"
      case Prim1(x)             => s"$x"
      case LabelLit(v)          => s"\"$v\""
      case Let1(x, ty, v, b)    => s"(let $x : $ty = $v; $b)"
      case U0(cv)               => s"(Ty $cv)"
      case U1                   => "Meta"
      case Pi(x, i, ty, b)      => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam1(x, i, ty, b)    => s"(\\${i.wrap(s"$x : $ty")} => $b)"
      case App1(fn, arg, Expl)  => s"($fn $arg)"
      case App1(fn, arg, i)     => s"($fn ${i.wrap(arg)})"
      case Fun(_, pty, _, rty)  => s"($pty -> $rty)"
      case TCon(x)              => s"$x"
      case CV1                  => "CV"
      case Comp                 => "Comp"
      case Lift(_, ty)          => s"^$ty"
      case Quote(tm)            => s"`$tm"
      case AppPruning(id, p)    => s"(?$id ...(${p.size}))"
      case Wk01(tm)             => s"$tm"
      case Wk11(tm)             => s"$tm"
      case Meta(id)             => s"?$id"
      case MetaPi(m, t, b)      => s"($t ${if m then "1" else "0"}-> $b)"
      case MetaLam(m, b)        => s"(\\${if m then "1" else "0"} => $b)"
      case MetaApp(f, Left(a))  => s"($f 0 $a)"
      case MetaApp(f, Right(a)) => s"($f 1 $a)"
      case PostponedCheck1(id)  => s"?p$id"
  export Tm1.*

  inline def quote(t: Tm0): Tm1 = t match
    case Splice(t) => t
    case t         => Quote(t)

  inline def splice(t: Tm1): Tm0 = t match
    case Quote(t) => t
    case t        => Splice(t)

  enum Locals:
    case LEmpty
    case LDef(locs: Locals, ty: Ty, value: Tm1)
    case LBind0(locs: Locals, ty: Ty, cv: CV)
    case LBind1(locs: Locals, ty: Ty)
  export Locals.*

  def Val(lev: Ty) = App1(Prim1(Name("Val")), lev, Expl)
