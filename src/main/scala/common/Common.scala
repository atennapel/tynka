package common

import scala.annotation.{targetName, unused}

object Common:
  def impossible(): Nothing = throw new Exception("impossible")

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

    def isOperator: Boolean = !x.head.isLetter

    def expose: String = x

    def fresh(implicit ns: List[Name]): Name =
      if !ns.contains(this) then this else next.fresh

    def next: Name =
      if x.last.isDigit then
        val n = x.reverse.takeWhile(_.isDigit).reverse
        val init = x.dropRight(n.length)
        Name(s"$init${n.toInt + 1}")
      else Name(s"${x}0")

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

    def fresh(implicit ns: List[Name]): Bind = this match
      case DoBind(x) => DoBind(x.fresh)
      case DontBind  => DontBind
  export Bind.*

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"
  export Icit.*

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
  enum Stage[+VF]:
    case S0(vf: VF)
    case S1 extends Stage[Nothing]

    def map[R](f: VF => R): Stage[R] = this match
      case S0(x) => S0(f(x))
      case S1    => S1

    def isS0: Boolean = this match
      case S0(_) => true
      case _     => false
  export Stage.*

  // primitives
  enum PrimName:
    case PVF
    case PV
    case PF

    case PVoid
    case PAbsurd

    case PUnitType
    case PUnit

    case PBool
    case PTrue
    case PFalse
    case PCaseBool

    case PInt
    case PPrimIntAdd
    case PPrimIntMul
    case PPrimIntSub
    case PPrimIntDiv
    case PPrimIntMod
    case PPrimIntEq
    case PPrimIntNeq
    case PPrimIntLt
    case PPrimIntGt
    case PPrimIntLeq
    case PPrimIntGeq

    case PList
    case PNil
    case PCons
    case PCaseList

    override def toString: String = this match
      case PVF => "VF"
      case PV  => "V"
      case PF  => "F"

      case PVoid   => "Void"
      case PAbsurd => "absurd"

      case PUnitType => "()"
      case PUnit     => "[]"

      case PBool     => "Bool"
      case PTrue     => "True"
      case PFalse    => "False"
      case PCaseBool => "caseBool"

      case PInt        => "Int"
      case PPrimIntAdd => "primIntAdd"
      case PPrimIntMul => "primIntMul"
      case PPrimIntSub => "primIntSub"
      case PPrimIntDiv => "primIntDiv"
      case PPrimIntMod => "primIntMod"
      case PPrimIntEq  => "primIntEq"
      case PPrimIntNeq => "primIntNeq"
      case PPrimIntLt  => "primIntLt"
      case PPrimIntGt  => "primIntGt"
      case PPrimIntLeq => "primIntLeq"
      case PPrimIntGeq => "primIntGeq"

      case PList     => "List"
      case PNil      => "Nil"
      case PCons     => "::"
      case PCaseList => "caseList"

    def isBinOp: Boolean = this match
      case PPrimIntAdd => true
      case PPrimIntMul => true
      case PPrimIntSub => true
      case PPrimIntDiv => true
      case PPrimIntMod => true
      case PPrimIntEq  => true
      case PPrimIntNeq => true
      case PPrimIntLt  => true
      case PPrimIntGt  => true
      case PPrimIntLeq => true
      case PPrimIntGeq => true
      case _           => false
  export PrimName.*
  object PrimName:
    def apply(x: Name): Option[PrimName] = x.expose match
      case "VF" => Some(PVF)
      case "V"  => Some(PV)
      case "F"  => Some(PF)

      case "Void"   => Some(PVoid)
      case "absurd" => Some(PAbsurd)

      case "()" => Some(PUnitType)
      case "[]" => Some(PUnit)

      case "Bool"     => Some(PBool)
      case "True"     => Some(PTrue)
      case "False"    => Some(PFalse)
      case "caseBool" => Some(PCaseBool)

      case "Int"        => Some(PInt)
      case "primIntAdd" => Some(PPrimIntAdd)
      case "primIntMul" => Some(PPrimIntMul)
      case "primIntSub" => Some(PPrimIntSub)
      case "primIntDiv" => Some(PPrimIntDiv)
      case "primIntMod" => Some(PPrimIntMod)
      case "primIntEq"  => Some(PPrimIntEq)
      case "primIntNeq" => Some(PPrimIntNeq)
      case "primIntLt"  => Some(PPrimIntLt)
      case "primIntGt"  => Some(PPrimIntGt)
      case "primIntLeq" => Some(PPrimIntLeq)
      case "primIntGeq" => Some(PPrimIntGeq)

      case "List"     => Some(PList)
      case "Nil"      => Some(PNil)
      case "::"       => Some(PCons)
      case "caseList" => Some(PCaseList)

      case _ => None
