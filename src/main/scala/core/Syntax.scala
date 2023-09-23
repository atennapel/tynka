package core

import common.Common.*

object Syntax:
  enum Tm0:
    case Var0(ix: Ix)
    case Prim0(name: Name)
    case Let0(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case Lam0(name: Bind, ty: Ty, body: Tm0)
    case App0(fn: Tm0, arg: Tm0)
    case Splice(tm: Tm1)
    case Wk10(tm: Tm0)

    override def toString: String = this match
      case Var0(ix)          => s"'$ix"
      case Prim0(x)          => s"$x"
      case Let0(x, ty, v, b) => s"(let $x : $ty := $v; $b)"
      case Lam0(x, ty, b)    => s"(\\($x : $ty). $b)"
      case App0(fn, arg)     => s"($fn $arg)"
      case Splice(tm)        => s"$$$tm"
      case Wk10(tm)          => s"$tm"
  export Tm0.*

  type Ty = Tm1
  type CV = Ty

  enum Tm1:
    case Var1(ix: Ix)
    case Prim1(name: Name)
    case Let1(name: Name, ty: Ty, value: Tm1, body: Tm1)

    case U0(cv: Tm1)
    case U1

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam1(name: Bind, icit: Icit, ty: Ty, body: Tm1)
    case App1(fn: Tm1, arg: Tm1, icit: Icit)

    case Fun(pty: Ty, cv: CV, rty: Ty)
    case CV1
    case Comp
    case Val
    case Lift(cv: CV, ty: Ty)

    case Quote(tm: Tm0)

    case Wk01(tm: Tm1)
    case Wk11(tm: Tm1)

    case Meta(id: MetaId)
    case MetaPi(meta: Boolean, ty: Ty, body: Ty)
    case MetaLam(meta: Boolean, body: Tm1)
    case MetaApp(fn: Tm1, arg: Either[Tm0, Tm1])
    case AppPruning(id: MetaId, pruning: Pruning)

    override def toString: String = this match
      case Var1(ix)             => s"'$ix"
      case Prim1(x)             => s"$x"
      case Let1(x, ty, v, b)    => s"(let $x : $ty = $v; $b)"
      case U0(cv)               => s"(Ty $cv)"
      case U1                   => "Meta"
      case Pi(x, i, ty, b)      => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam1(x, i, ty, b)    => s"(\\${i.wrap(s"$x : $ty")}. $b)"
      case App1(fn, arg, Expl)  => s"($fn $arg)"
      case App1(fn, arg, i)     => s"($fn ${i.wrap(arg)})"
      case Fun(pty, _, rty)     => s"($pty -> $rty)"
      case CV1                  => "CV"
      case Comp                 => "Comp"
      case Val                  => "Val"
      case Lift(_, ty)          => s"^$ty"
      case Quote(tm)            => s"`$tm"
      case AppPruning(id, _)    => s"(?$id ...)"
      case Wk01(tm)             => s"$tm"
      case Wk11(tm)             => s"$tm"
      case Meta(id)             => s"?$id"
      case MetaPi(m, t, b)      => s"($t ${if m then "1" else "0"}-> $b)"
      case MetaLam(m, b)        => s"(\\${if m then "1" else "0"}. $b)"
      case MetaApp(f, Left(a))  => s"($f 0 $a)"
      case MetaApp(f, Right(a)) => s"($f 1 $a)"
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
