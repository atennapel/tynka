package jvmir

import common.Common.{impossible, PrimName}

object Syntax:
  type LName = Int
  type GName = String

  enum Ty:
    case TCon(x: GName)
    case TConCon(x: GName, c: GName)
    case TForeign(cls: String)
    case TArray(ty: Ty)

    override def toString: String = this match
      case TCon(x)        => s"$x"
      case TConCon(x, cx) => s"Con($x,$cx)"
      case TForeign(x)    => s"Foreign($x)"
      case TArray(ty)     => s"Array($ty)"

    def tdef: TDef = TDef(this)

    def dataGlobals: Set[GName] = this match
      case TCon(x)       => Set(x)
      case TConCon(x, _) => Set(x)
      case TForeign(cls) => Set.empty
      case TArray(ty)    => ty.dataGlobals
  export Ty.*

  final case class TDef(ps: Option[List[Ty]], rt: Ty):
    override def toString: String = ps match
      case None => rt.toString
      case _    => s"(${ps.get.mkString(", ")}) -> $rt"
    def head: Ty = ps.get.head
    def tail: TDef = TDef(ps.get.tail, rt)
    def ty: Ty =
      if ps.nonEmpty then impossible()
      else rt
    def drop(n: Int): TDef = TDef(ps.get.drop(n), rt)
    def params: List[Ty] = ps.getOrElse(Nil)

    def dataGlobals: Set[GName] =
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

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case DDef(
        name: GName,
        gen: Boolean,
        ty: TDef,
        value: Tm
    )
    case DData(
        name: GName,
        cs: List[(GName, List[Ty])]
    )

    def globals: Set[GName] = this match
      case DDef(name, gen, ty, value) => value.globals
      case DData(name, cs)            => Set.empty

    def dataGlobals: Set[GName] = this match
      case DDef(name, gen, ty, value) => ty.dataGlobals ++ value.dataGlobals
      case DData(name, cs) =>
        cs.flatMap((_, as) => as.flatMap(_.dataGlobals)).toSet

    override def toString: String = this match
      case DDef(x, _, TDef(None, t), v) => s"def $x : $t = $v"
      case DDef(x, _, t, v) =>
        s"def $x (${t.params.mkString(", ")}) : ${t.rt} = $v"
      case DData(x, Nil) => s"data $x"
      case DData(x, cs) =>
        s"data $x = ${cs
            .map((x, ts) => s"$x${if ts.isEmpty then "" else " "}${ts.mkString(" ")}")
            .mkString(" | ")}"
  export Def.*

  enum Tm:
    case Arg(ix: Int)
    case Var(name: LName)
    case Global(name: GName, ty: Ty)

    case Let(name: LName, ty: Ty, value: Tm, body: Tm)

    case GlobalApp(
        name: GName,
        ty: TDef,
        tc: Boolean,
        as: List[Tm]
    )

    case IntLit(value: Int)
    case BoolLit(value: Boolean)
    case StringLit(value: String)

    case Con(name: GName, con: GName, args: List[Tm])
    case Field(dty: GName, con: GName, scrut: Tm, ix: Int)
    case Match(
        dty: GName,
        ty: Ty,
        x: LName,
        scrut: Tm,
        cs: List[(GName, Tm)],
        other: Option[Tm]
    )

    case Foreign(rt: Ty, cmd: String, args: List[(Tm, Ty)])

    def globals: Set[GName] = this match
      case Arg(ix)          => Set.empty
      case Var(name)        => Set.empty
      case IntLit(value)    => Set.empty
      case BoolLit(value)   => Set.empty
      case StringLit(value) => Set.empty

      case Global(name, ty) => Set(name)
      case GlobalApp(name, ty, tc, as) =>
        Set(name) ++ as.flatMap(_.globals)

      case Let(name, ty, value, body) =>
        value.globals ++ body.globals
      case Con(name, con, args) =>
        args.flatMap(_.globals).toSet
      case Field(dty, con, scrut, ix) =>
        scrut.globals
      case Match(dty, ty, x, scrut, cs, other) =>
        scrut.globals ++ cs.flatMap((_, t) => t.globals) ++ other
          .map(_.globals)
          .getOrElse(Set.empty)
      case Foreign(rt, cmd, args) =>
        args.flatMap((t, _) => t.globals).toSet

    def dataGlobals: Set[GName] = this match
      case Arg(ix)          => Set.empty
      case Var(name)        => Set.empty
      case IntLit(value)    => Set.empty
      case BoolLit(value)   => Set.empty
      case StringLit(value) => Set.empty

      case Global(name, ty)     => ty.dataGlobals
      case Con(name, con, args) => Set(name) ++ args.flatMap(_.dataGlobals)
      case Field(dty, con, scrut, ix) => Set(dty) ++ scrut.dataGlobals
      case Match(dty, ty, x, scrut, cs, other) =>
        Set(dty) ++ ty.dataGlobals ++ scrut.dataGlobals ++ cs.flatMap((_, t) =>
          t.dataGlobals
        ) ++ other.map(_.dataGlobals).getOrElse(Set.empty)
      case Let(name, ty, value, body) =>
        ty.dataGlobals ++ value.dataGlobals ++ body.dataGlobals
      case GlobalApp(name, ty, tc, as) =>
        ty.dataGlobals ++ as.flatMap(_.dataGlobals)
      case Foreign(rt, cmd, args) =>
        rt.dataGlobals ++ args.flatMap((a, b) => a.dataGlobals ++ b.dataGlobals)

    override def toString: String = this match
      case Arg(i)          => s"'arg$i"
      case Var(x)          => s"'$x"
      case Global(x, _)    => s"$x"
      case Let(x, t, v, b) => s"(let $x : $t = $v; $b)"

      case IntLit(v)    => s"$v"
      case BoolLit(v)   => s"$v"
      case StringLit(v) => s"\"$v\""

      case GlobalApp(x, _, tc, as) =>
        s"(${if tc then "[tailcall] " else ""}$x(${as.mkString(", ")}))"

      case Con(_, "Z", Nil) => "0"
      case full @ Con(_, "S", as @ List(n)) =>
        def tryNat(n: Tm): Option[Int] = n match
          case Con(_, "Z", Nil)     => Some(0)
          case Con(_, "S", List(n)) => tryNat(n).map(_ + 1)
          case _                    => None
        tryNat(full).map(_.toString).getOrElse(s"(con S ${as.mkString(" ")})")
      case Con(x, cx, Nil)   => s"(con $cx)"
      case Con(x, cx, as)    => s"(con $cx ${as.mkString(" ")})"
      case Field(_, _, t, i) => s"(field #$i $t)"
      case Match(_, _, x, scrut, cs, other) =>
        s"(match $x = $scrut; ${cs
            .map((c, b) => s"| $c $b")
            .mkString(" ")} ${other.map(t => s"| $t").getOrElse("")})"

      case Foreign(rt, cmd, Nil) =>
        s"(foreign $rt $cmd)"
      case Foreign(rt, cmd, as) =>
        s"(foreign $rt $cmd ${as.map((v, t) => s"$v").mkString(" ")})"
  export Tm.*
