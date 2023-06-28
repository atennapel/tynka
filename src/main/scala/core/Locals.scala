package core

import common.Common.*
import Syntax.*

enum Locals:
  case Empty
  case Bound(locals: Locals, x: Bind, ty: Ty, stage: CStage)
  case Defined(locals: Locals, x: Name, ty: Ty, stage: CStage, tm: Tm)

  def closeTy(b: Ty): Ty = this match
    case Empty                   => b
    case Bound(ls, x, a, _)      => ls.closeTy(Pi(x, Expl, a, b))
    case Defined(ls, x, a, s, v) => ls.closeTy(Let(x, a, s, Irrelevant, v, b))

  def names: List[Name] = this match
    case Empty                   => Nil
    case Bound(ls, x, _, _)      => x.toName :: ls.names
    case Defined(ls, x, _, _, _) => x :: ls.names
export Locals.*
