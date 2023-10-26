package jvmir

import common.Common.*

object Syntax:
  type ArgIx = Int
  type LName = Int

  enum Ty:
    case TCon(name: Name)

    override def toString: String = this match
      case TCon(name) => s"$name"

    def dataGlobals: Set[Name] = this match
      case TCon(x) => Set(x)
  export Ty.*

  final case class TDef(ps: Option[List[Ty]], rt: Ty):
    override def toString: String = ps match
      case None     => s"$rt"
      case Some(ps) => s"${ps.mkString("(", ", ", ")")} -> $rt"
    def dataGlobals: Set[Name] =
      ps.map(_.flatMap(_.dataGlobals))
        .getOrElse(Set.empty)
        .toSet ++ rt.dataGlobals
  object TDef:
    def apply(rt: Ty): TDef = TDef(None, rt)
    def apply(t1: Ty, t2: Ty): TDef = TDef(List(t1), t2)
    def apply(t1: Ty, t2: TDef): TDef =
      t2.ps match
        case None     => TDef(List(t1), t2.rt)
        case Some(ps) => TDef(t1 :: ps, t2.rt)
    def apply(ps: List[Ty], t2: Ty): TDef = TDef(Some(ps), t2)
    def apply(ps: List[Ty], t2: TDef): TDef =
      t2.ps match
        case None      => TDef(ps, t2.rt)
        case Some(ps2) => TDef(ps ++ ps2, t2.rt)

  enum Def:
    case DData(name: Name, cons: List[(Name, List[(Bind, Ty)])])
    case DDef(name: Name, ty: TDef, value: Tm)

    def globals: Set[Name] = this match
      case DDef(name, ty, value) => value.globals
      case DData(name, cs)       => Set.empty

    def dataGlobals: Set[Name] = this match
      case DDef(name, ty, value) => ty.dataGlobals ++ value.dataGlobals
      case DData(name, cs) =>
        cs.flatMap((_, as) => as.flatMap((_, t) => t.dataGlobals)).toSet

    override def toString: String = this match
      case DData(x, Nil) => s"data $x"
      case DData(x, cs) =>
        val scs = cs
          .map { (c, as) =>
            as match
              case Nil => s"$c"
              case as =>
                val sas = as
                  .map {
                    case (DontBind, t)  => s"$t"
                    case (DoBind(x), t) => s"($x : $t)"
                  }
                  .mkString(" ")
                s"$c $sas"
          }
          .mkString(" | ")
        s"data $x = $scs"
      case DDef(x, t, v) =>
        val sps = t.ps.map(_.mkString(" ")).getOrElse("")
        s"def $x${if t.ps.isEmpty then "" else " "}$sps : ${t.rt} = $v"
  export Def.*

  enum Tm:
    case Arg(ix: ArgIx)
    case Var(name: LName)
    case Global(name: Name, ty: Ty)

    case Let(name: LName, ty: Ty, value: Tm, body: Tm)

    case Join(name: LName, ps: List[(LName, Ty)], ty: Ty, value: Tm, body: Tm)
    case JoinRec(
        name: LName,
        ps: List[(LName, Ty)],
        ty: Ty,
        value: Tm,
        body: Tm
    )
    case Jump(name: LName, args: List[Tm])

    case GlobalApp(name: Name, ty: TDef, as: List[Tm])

    case Con(con: Name, args: List[Tm])
    case Field(scrut: Tm, ty: Ty, ix: Int)
    case Match(
        scrut: Tm,
        ty: Ty,
        con: Name,
        name: LName,
        body: Tm,
        other: Tm
    )

    def globals: Set[Name] = this match
      case Arg(ix)   => Set.empty
      case Var(name) => Set.empty

      case Global(x, ty)        => Set(x)
      case GlobalApp(x, ty, as) => Set(x) ++ as.flatMap(_.globals)

      case Let(name, ty, value, body) =>
        value.globals ++ body.globals

      case Join(x, ps, ty, v, b)  => v.globals ++ b.globals
      case JoinRec(_, _, _, v, b) => v.globals ++ b.globals
      case Jump(_, as)            => as.flatMap(_.globals).toSet

      case Con(_, as)              => as.flatMap(_.globals).toSet
      case Field(s, _, _)          => s.globals
      case Match(s, _, _, _, b, o) => s.globals ++ b.globals ++ o.globals

    def dataGlobals: Set[Name] = this match
      case Arg(ix)   => Set.empty
      case Var(name) => Set.empty

      case Global(x, ty)        => ty.dataGlobals
      case GlobalApp(x, ty, as) => ty.dataGlobals ++ as.flatMap(_.dataGlobals)

      case Let(name, ty, value, body) =>
        ty.dataGlobals ++ value.dataGlobals ++ body.dataGlobals

      case Join(x, ps, ty, v, b) =>
        ps.flatMap((_, t) => t.dataGlobals)
          .toSet ++ v.dataGlobals ++ b.dataGlobals
      case JoinRec(_, ps, ty, v, b) =>
        ps.flatMap((_, t) => t.dataGlobals)
          .toSet ++ v.dataGlobals ++ b.dataGlobals
      case Jump(_, as) => as.flatMap(_.dataGlobals).toSet

      case Con(_, as)      => as.flatMap(_.dataGlobals).toSet
      case Field(s, ty, _) => s.dataGlobals ++ ty.dataGlobals
      case Match(s, t, bt, _, b, o) =>
        t.dataGlobals ++ s.dataGlobals ++ b.dataGlobals ++ o.dataGlobals

    override def toString: String = this match
      case Arg(i)       => s"'arg$i"
      case Var(x)       => s"'$x"
      case Global(x, _) => s"$x"

      case Let(x, t, v, b) => s"(let $x : $t = $v; $b)"

      case Join(x, ps, t, v, b) =>
        s"(join $x${if ps.isEmpty then "" else " "}${ps
            .map((x, t) => s"($x : $t)")
            .mkString(" ")} : $t = $v; $b)"
      case JoinRec(x, ps, t, v, b) =>
        s"(join rec $x${if ps.isEmpty then "" else " "}${ps
            .map((x, t) => s"($x : $t)")
            .mkString(" ")} : $t = $v; $b)"
      case Jump(x, as) => s"jump@$x(${as.mkString(", ")})"

      case GlobalApp(x, _, as) =>
        s"$x(${as.mkString(", ")})"

      case Con(x, Nil) => s"$x"
      case Con(x, as)  => s"($x ${as.mkString(" ")})"
      case Match(scrut, _, c, x, b, e) =>
        s"(match $scrut | $c as '$x => $b | _ => $e)"
      case Field(value, _, ix) => s"(#$ix $value)"
  export Tm.*
