package common

import scala.annotation.{targetName, unused}

object Common:
  def impossible(): Nothing = throw new Exception("impossible")
  def mapFst[A, B, C](f: A => C, p: (A, B)): (C, B) = (f(p._1), p._2)
  def mapSnd[A, B, C](f: B => C, p: (A, B)): (A, C) = (p._1, f(p._2))

  type PosInfo = (Int, Int) // (line, col)

  // debruijn indeces
  opaque type Ix = Int
  inline def ix0: Ix = 0
  inline def mkIx(i: Int): Ix = i
  extension (i: Ix)
    inline def expose: Int = i
    inline def +(o: Int): Ix = i + o

  // levels
  opaque type Lvl = Int
  inline def lvl0: Lvl = 0
  inline def mkLvl(i: Int): Lvl = i
  extension (l: Lvl)
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    inline def -(o: Int): Lvl = l - o
    @targetName("exposeLvl")
    inline def expose: Int = l
    inline def toIx(implicit k: Lvl): Ix = k - l - 1

  // names
  case class Name(x: String):
    override def toString: String =
      if !isOperator then x else s"($x)"
    def isOperator: Boolean = !x.head.isLetter && x.head != '_'
    def expose: String = x

  enum Bind:
    case DontBind
    case DoBind(name: Name)

    override def toString: String = this match
      case DontBind  => "_"
      case DoBind(x) => x.toString

    def toName: Name = this match
      case DontBind  => Name("_")
      case DoBind(x) => x

    def toSet: Set[Name] = this match
      case DontBind  => Set.empty
      case DoBind(x) => Set(x)
  export Bind.*

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"

    def toPiIcit: PiIcit = this match
      case Expl => PiExpl
      case Impl => PiImpl(false)

    def eqPiIcit(i: PiIcit): Boolean = (this, i) match
      case (Expl, PiExpl)    => true
      case (Impl, PiImpl(_)) => true
      case _                 => false
  export Icit.*

  enum PiIcit:
    case PiExpl
    case PiImpl(search: Boolean)

    def wrap(x: Any): String = this match
      case PiExpl        => s"($x)"
      case PiImpl(false) => s"{$x}"
      case PiImpl(true)  => s"{auto $x}"

    def toIcit: Icit = this match
      case PiExpl         => Expl
      case PiImpl(search) => Impl

    def isAuto: Boolean = this match
      case PiExpl => false
      case PiImpl(auto) => auto
  export PiIcit.*

  // pruning
  type Pruning = List[Option[Icit]]

  opaque type RevPruning = Pruning
  extension (r: RevPruning)
    @targetName("exposeRevPruning")
    inline def expose: Pruning = r
  def revPruning(p: Pruning): RevPruning = p.reverse

  // meta ids
  opaque type MetaId = Int
  inline def metaId(id: Int): MetaId = id
  extension (id: MetaId)
    @targetName("exposeMetaId")
    inline def expose: Int = id

  // stages
  enum Stage[+CV]:
    case SMeta extends Stage[Nothing]
    case STy(cv: CV)

    override def toString: String = this match
      case SMeta   => "Meta"
      case STy(cv) => s"Ty $cv"

    def map[CV2](f: CV => CV2): Stage[CV2] = this match
      case SMeta   => SMeta
      case STy(cv) => STy(f(cv))

    def fold[R](m: R, t: CV => R): R = this match
      case SMeta   => m
      case STy(cv) => t(cv)

    def isMeta: Boolean = this match
      case SMeta => true
      case _     => false
  export Stage.*

  // usages
  enum Usage:
    case Zero
    case One
    case Many

    override def toString: String = this match
      case Zero => "0"
      case One  => "1"
      case Many => "*"

    def prefix: String = this match
      case Zero => "0 "
      case One  => "1 "
      case Many => ""

    def +(b: Usage): Usage = (this, b) match
      case (Many, _)  => Many
      case (_, Many)  => Many
      case (One, One) => Many
      case (One, _)   => One
      case (_, b)     => b

    def *(b: Usage): Usage = (this, b) match
      case (Zero, _) => Zero
      case (_, Zero) => Zero
      case (One, b)  => b
      case (a, One)  => a
      case _         => Many

    def *(b: Uses): Uses = Uses(b.expose.map(this * _))

    def <=(b: Usage): Boolean =
      (this == b) || ((this == Zero || this == One) && b == Many)

    def lub(b: Usage): Usage = if this == b then this else Many
  export Usage.*

  final case class Uses(expose: List[Usage]):
    def size: Int = expose.size
    def head: Usage = expose.head
    def tail: Uses = Uses(expose.tail)

    private def guardUsesZip(b: Uses): Unit =
      if size != b.size then impossible()

    def +(b: Uses): Uses =
      guardUsesZip(b)
      Uses(expose.zip(b.expose).map(_ + _))

    def lub(b: Uses): Uses =
      guardUsesZip(b)
      Uses(expose.zip(b.expose).map(_ lub _))

    def uncons: (Usage, Uses) = (expose.head, Uses(expose.tail))
    def uncons2: (Usage, Usage, Uses) =
      (expose.tail.head, expose.head, Uses(expose.tail.tail))

  object Uses:
    def apply(size: Int): Uses = Uses((0 until size).map(_ => Zero).toList)

    def lub(uses: List[Uses]): Uses = uses.reduce(_ lub _)

  // primitives
  enum PrimName:
    case PCV
    case PVal
    case PComp

    case PUnitType
    case PUnit
    case PConsumeLinearUnit
    case PUnsafeLinearFunction

    case PIO
    case PReturnIO
    case PBindIO
    case PRunIO

    case PArray

    case PLabel
    case PEqLabel
    case PAppendLabel

    case PForeignType

    case PBoolM
    case PTrueM
    case PFalseM
    case PElimBoolM

    case PHId
    case PRefl
    case PElimHId

    case PIFixM
    case PIInM
    case PElimIFixM

    case PCon
    case PConExpose

    override def toString: String = this match
      case PCV   => "CV"
      case PVal  => "Val"
      case PComp => "Comp"

      case PUnitType             => "()"
      case PUnit                 => "[]"
      case PConsumeLinearUnit    => "consumeLinearUnit"
      case PUnsafeLinearFunction => "unsafeLinearFunction"

      case PIO       => "IO"
      case PReturnIO => "returnIO"
      case PBindIO   => "bindIO"
      case PRunIO    => "unsafePerformIO"

      case PArray => "Array"

      case PLabel       => "Label"
      case PEqLabel     => "eqLabel"
      case PAppendLabel => "appendLabel"

      case PForeignType => "Foreign"

      case PBoolM     => "BoolM"
      case PTrueM     => "TrueM"
      case PFalseM    => "FalseM"
      case PElimBoolM => "elimBoolM"

      case PHId     => "HId"
      case PRefl    => "Refl"
      case PElimHId => "elimHId"

      case PIFixM     => "IFixM"
      case PIInM      => "IInM"
      case PElimIFixM => "elimIFixM"

      case PCon       => "Con"
      case PConExpose => "exposeCon"
  export PrimName.*
  object PrimName:
    val primNames: List[Name] =
      List(
        "CV",
        "Val",
        "Comp",
        "()",
        "[]",
        "consumeLinearUnit",
        "unsafeLinearFunction",
        "IO",
        "returnIO",
        "bindIO",
        "unsafePerformIO",
        "Array",
        "Label",
        "eqLabel",
        "appendLabel",
        "Foreign",
        "BoolM",
        "TrueM",
        "FalseM",
        "elimBoolM",
        "HId",
        "Refl",
        "elimHId",
        "IFixM",
        "IInM",
        "elimIFixM",
        "Con",
        "exposeCon"
      )
        .map(Name.apply)

    def apply(x: Name): Option[PrimName] = x.expose match
      case "CV"   => Some(PCV)
      case "Val"  => Some(PVal)
      case "Comp" => Some(PComp)

      case "()"                   => Some(PUnitType)
      case "[]"                   => Some(PUnit)
      case "consumeLinearUnit"    => Some(PConsumeLinearUnit)
      case "unsafeLinearFunction" => Some(PUnsafeLinearFunction)

      case "IO"              => Some(PIO)
      case "returnIO"        => Some(PReturnIO)
      case "bindIO"          => Some(PBindIO)
      case "unsafePerformIO" => Some(PRunIO)

      case "Array" => Some(PArray)

      case "Label"       => Some(PLabel)
      case "eqLabel"     => Some(PEqLabel)
      case "appendLabel" => Some(PAppendLabel)

      case "Foreign" => Some(PForeignType)

      case "BoolM"     => Some(PBoolM)
      case "TrueM"     => Some(PTrueM)
      case "FalseM"    => Some(PFalseM)
      case "elimBoolM" => Some(PElimBoolM)

      case "HId"     => Some(PHId)
      case "Refl"    => Some(PRefl)
      case "elimHId" => Some(PElimHId)

      case "IFixM"     => Some(PIFixM)
      case "IInM"      => Some(PIInM)
      case "elimIFixM" => Some(PElimIFixM)

      case "Con"       => Some(PCon)
      case "exposeCon" => Some(PConExpose)

      case _ => None
