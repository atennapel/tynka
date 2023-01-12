package jvmir

import ir.Syntax.{GName, Op}

object Syntax:
  enum Ty:
    case TBool
    case TInt
    case TPair
    case TEither
    case TList

    override def toString: String = this match
      case TBool   => "Bool"
      case TInt    => "Int"
      case TPair   => "Pair"
      case TEither => "Either"
      case TList   => "List"
  export Ty.*

  final case class TDef(params: List[Ty], retrn: Ty):
    override def toString: String = params match
      case Nil => retrn.toString
      case ps  => s"(${ps.mkString(", ")}) -> $retrn"
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)

  enum Tm:
    case Arg(ix: Int, ty: Ty)
    case Local(name: Int, ty: Ty)
    case Global(name: GName, tailRecursive: Boolean, ty: TDef, args: List[Tm])
    case Let(name: Int, ty: Ty, value: Tm, body: Tm)

    case Pair(fst: Tm, snd: Tm)
    case Fst(tm: Tm)
    case Snd(tm: Tm)

    case True
    case False
    case If(ty: Ty, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case IntLit(value: Int)
    case Binop(op: Op, left: Tm, right: Tm)

    case NilL(ty: Ty)
    case ConsL(ty: Ty, head: Tm, tail: Tm)
    case CaseL(scrut: Tm, et: Ty, nil: Tm, hd: Int, tl: Int, cons: Tm)

    case LeftE(t1: Ty, t2: Ty, v: Tm)
    case RightE(t1: Ty, t2: Ty, v: Tm)
    case CaseE(t1: Ty, t2: Ty, scut: Tm, x: Int, l: Tm, y: Int, r: Tm)

    case Box(ty: Ty, tm: Tm)
    case Unbox(ty: Ty, tm: Tm)

    case Absurd(ty: Ty)

    override def toString: String = this match
      case Arg(ix, _)            => s"'arg$ix"
      case Local(x, _)           => s"'$x"
      case Global(x, tr, _, Nil) => s"$x${if tr then "{tr}" else ""}"
      case Global(x, tr, _, as) =>
        s"$x${if tr then "{tr}" else ""}(${as.mkString(", ")})"
      case Let(x, t, v, b) =>
        s"(let '$x : $t = $v in $b)"

      case Pair(fst, snd) => s"($fst, $snd)"
      case Fst(t)         => s"(fst $t)"
      case Snd(t)         => s"(snd $t)"

      case True           => "True"
      case False          => "False"
      case If(_, c, a, b) => s"(if $c then $a else $b)"

      case IntLit(n)       => s"$n"
      case Binop(op, a, b) => s"($a $op $b)"

      case NilL(_)          => "Nil"
      case ConsL(_, hd, tl) => s"(Cons $hd $tl)"
      case CaseL(scrut, _, nil, hd, tl, cons) =>
        s"(caseList $scrut $nil ($hd $tl. $cons))"

      case LeftE(_, _, v)  => s"(Left $v)"
      case RightE(_, _, v) => s"(Right $v)"
      case CaseE(_, _, scrut, x, l, y, r) =>
        s"(caseEither $scrut ($x. $l) ($y. $r))"

      case Box(ty, tm)   => s"(box {$ty} $tm)"
      case Unbox(ty, tm) => s"(unbox {$ty} $tm)"

      case Absurd(ty) => s"absurd"
  export Tm.*

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")

    def toList: List[Def] = defs

  enum Def:
    case DDef(
        name: GName,
        generated: Boolean,
        params: List[Ty],
        retrn: Ty,
        value: Tm
    )

    override def toString: String = this match
      case DDef(x, g, Nil, rt, v) =>
        s"${if g then "(gen) " else ""}$x : $rt = $v;"
      case DDef(x, g, ps, rt, v) =>
        s"${if g then "(gen) " else ""}$x (${ps.mkString(", ")}) : $rt = $v;"
  export Def.*
