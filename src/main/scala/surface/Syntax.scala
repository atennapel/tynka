package surface

import common.Common.*
import scala.annotation.tailrec

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case DDef(
        pos: PosInfo,
        name: Name,
        rec: Boolean,
        meta: Boolean,
        ty: Option[Ty],
        value: Tm
    )

    override def toString: String = this match
      case DDef(_, x, rec, m, Some(t), v) =>
        s"def ${if rec then "rec " else ""}$x : $t ${if m then "" else ":"}= $v"
      case DDef(_, x, rec, m, None, v) =>
        s"def ${if rec then "rec " else ""}$x ${if m then "" else ":"}= $v"
  export Def.*

  enum ArgInfo:
    case ArgNamed(name: Name)
    case ArgIcit(icit: Icit)
  export ArgInfo.*

  final case class DataCon(pos: PosInfo, name: Name, args: List[(Bind, Ty)]):
    override def toString: String = this match
      case DataCon(_, x, Nil) => s"$x"
      case DataCon(_, x, as) =>
        def goArg(a: (Bind, Ty)): String = a._1 match
          case DontBind  => s"${a._2}"
          case DoBind(x) => s"($x : ${a._2})"
        s"$x ${as.map(goArg).mkString(" ")}"

  enum Pat:
    case PVar(name: Bind)
    case PCon(con: Name, args: List[Pat])

    override def toString: String = this match
      case PVar(x)       => s"$x"
      case PCon(c, Nil)  => s"$c"
      case PCon(c, args) => s"($c ${args.mkString(" ")})"
  export Pat.*

  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let(
        name: Name,
        rec: Boolean,
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

    case Data(name: Bind, cons: List[DataCon])
    case Con(name: Name, args: List[Tm])
    case Match(
        scrut: List[Tm],
        pats: List[(PosInfo, List[Pat], Tm)]
    )

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
      case Let(x, rec, m, ty, v, b) =>
        s"(let ${if rec then "rec " else ""}$x${ty
            .map(t => s" : $t")
            .getOrElse("")} ${if m then "" else ":"}= $v; $b)"
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
      case Data(x, Nil)                => s"(data $x.)"
      case Data(x, cs) => s"(data $x. ${cs.map(_.toString).mkString(" | ")})"
      case Con(x, Nil) => s"(con $x)"
      case Con(x, as)  => s"(con $x ${as.mkString(" ")})"
      case Match(scrut, pats) =>
        s"(match${if scrut.isEmpty then "" else " "}${scrut.mkString(", ")}${
            if pats.isEmpty then "" else " "
          }${pats.map((_, ps, b) => s"| ${ps.mkString(", ")}. $b").mkString(" ")})"
      case Lift(ty)      => s"^$ty"
      case Quote(tm)     => s"`$tm"
      case Splice(tm)    => s"$$$tm"
      case Hole(None)    => s"_"
      case Hole(Some(x)) => s"_$x"
      case Pos(_, tm)    => s"$tm"
  export Tm.*
