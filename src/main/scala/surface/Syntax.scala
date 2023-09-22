package surface

import common.Common.*

object Syntax:
  enum ArgInfo:
    case ArgNamed(name: Name)
    case ArgIcit(icit: Icit)
  export ArgInfo.*

  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(
        name: Name,
        meta: Boolean,
        ty: Option[Ty],
        value: Tm,
        body: Tm
    )

    case U0(cv: Ty)
    case U1
    case CV
    case Comp
    case Val

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)

    case Lift(ty: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    override def toString: String = this match
      case Var(x) => s"$x"
      case Let(x, m, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} ${if m then "" else ":"}= $v; $b)"
      case U0(cv)                         => s"(Ty $cv)"
      case U1                             => "Meta"
      case CV                             => "CV"
      case Comp                           => "Comp"
      case Val                            => "Val"
      case Pi(DontBind, Expl, ty, b)      => s"($ty -> $b)"
      case Pi(x, i, ty, b)                => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(x, ArgIcit(Expl), None, b) => s"(\\$x. $b)"
      case Lam(x, ArgIcit(i), ty, b) =>
        s"(\\${i.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")}")}. $b)"
      case Lam(x, ArgNamed(y), ty, b) =>
        s"(\\${Impl.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")} = $y")}. $b)"
      case App(fn, arg, ArgIcit(Expl)) => s"($fn $arg)"
      case App(fn, arg, ArgIcit(Impl)) => s"($fn ${Impl.wrap(arg)})"
      case App(fn, arg, ArgNamed(x))   => s"($fn ${Impl.wrap(s"$x = $arg")})"
      case Lift(ty)                    => s"^$ty"
      case Quote(tm)                   => s"`$tm"
      case Splice(tm)                  => s"$$$tm"
      case Hole(None)                  => s"_"
      case Hole(Some(x))               => s"_$x"
      case Pos(_, tm)                  => s"$tm"
  export Tm.*
