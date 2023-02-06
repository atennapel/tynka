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
  enum Stage[+VF]:
    case SMeta extends Stage[Nothing]
    case STy(vf: VF)

    override def toString: String = this match
      case SMeta   => "Meta"
      case STy(vf) => s"Ty $vf"

    def map[VF2](f: VF => VF2): Stage[VF2] = this match
      case SMeta   => SMeta
      case STy(vf) => STy(f(vf))

    def isMeta: Boolean = this match
      case SMeta => true
      case _     => false
  export Stage.*

  // primitives
  enum PrimName:
    case PVF
    case PVal
    case PFun
    case PTFun

    case PTBox
    case PBox
    case PUnbox

    case PUnitType
    case PUnit

    case PInt
    case PIntAdd
    case PIntSub
    case PIntMul
    case PIntDiv
    case PIntMod

    case PIntEq
    case PIntNeq
    case PIntLt
    case PIntGt
    case PIntLeq
    case PIntGeq

    case PIO
    case PReturnIO
    case PBindIO

    override def toString: String = this match
      case PVF   => "VF"
      case PVal  => "Val"
      case PFun  => "Fun"
      case PTFun => "TFun"

      case PTBox  => "Box"
      case PBox   => "box"
      case PUnbox => "unbox"

      case PUnitType => "()"
      case PUnit     => "[]"

      case PInt    => "Int"
      case PIntAdd => "intAdd"
      case PIntSub => "intSub"
      case PIntMul => "intMul"
      case PIntDiv => "intDiv"
      case PIntMod => "intMod"

      case PIntEq  => "intEq"
      case PIntNeq => "intNeq"
      case PIntLt  => "intLt"
      case PIntGt  => "intGt"
      case PIntLeq => "intLeq"
      case PIntGeq => "intGeq"

      case PIO       => "IO"
      case PReturnIO => "returnIO"
      case PBindIO   => "bindIO"
  export PrimName.*
  object PrimName:
    def apply(x: Name): Option[PrimName] = x.expose match
      case "VF"   => Some(PVF)
      case "Val"  => Some(PVal)
      case "Fun"  => Some(PFun)
      case "TFun" => Some(PTFun)

      case "Box"   => Some(PTBox)
      case "box"   => Some(PBox)
      case "unbox" => Some(PUnbox)

      case "()" => Some(PUnitType)
      case "[]" => Some(PUnit)

      case "Int"    => Some(PInt)
      case "intAdd" => Some(PIntAdd)
      case "intSub" => Some(PIntSub)
      case "intMul" => Some(PIntMul)
      case "intDiv" => Some(PIntDiv)
      case "intMod" => Some(PIntMod)

      case "intEq"  => Some(PIntEq)
      case "intNeq" => Some(PIntNeq)
      case "intLt"  => Some(PIntLt)
      case "intGt"  => Some(PIntGt)
      case "intLeq" => Some(PIntLeq)
      case "intGeq" => Some(PIntGeq)

      case "IO"       => Some(PIO)
      case "returnIO" => Some(PReturnIO)
      case "bindIO"   => Some(PBindIO)

      case _ => None
