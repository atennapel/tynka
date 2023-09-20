package core

import common.Common.*

object Syntax:
  enum Tm0:
    case Var0(ix: Ix)
    case Let0(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case Lam0(name: Bind, ty: Ty, body: Tm0)
    case App0(fn: Tm0, arg: Tm0)
    case Splice(tm: Tm1)
    case Wk10(tm: Tm0)
  export Tm0.*

  type Ty = Tm1
  type CV = Ty

  enum Tm1:
    case Var1(ix: Ix)
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

    case AppPruning(tm: Tm1, pruning: Pruning)

    case Wk01(tm: Tm1)
    case Wk11(tm: Tm1)

    case Meta(id: MetaId)
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
