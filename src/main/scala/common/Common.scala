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
    def isOperator: Boolean = !x.head.isLetter
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
  enum Stage[+CV]:
    case SMeta extends Stage[Nothing]
    case STy(cv: CV)

    override def toString: String = this match
      case SMeta   => "Meta"
      case STy(cv) => s"Ty $cv"

    def map[CV2](f: CV => CV2): Stage[CV2] = this match
      case SMeta   => SMeta
      case STy(cv) => STy(f(cv))

    def isMeta: Boolean = this match
      case SMeta => true
      case _     => false
  export Stage.*

  // primitives
  enum PrimName:
    case PCV
    case PVal
    case PComp
    case PFun

    case PUnitType
    case PUnit

    override def toString: String = this match
      case PCV   => "CV"
      case PVal  => "Val"
      case PComp => "Comp"
      case PFun  => "Fun"

      case PUnitType => "()"
      case PUnit     => "[]"
  export PrimName.*
  object PrimName:
    def apply(x: Name): Option[PrimName] = x.expose match
      case "CV"   => Some(PCV)
      case "Val"  => Some(PVal)
      case "Comp" => Some(PComp)
      case "Fun"  => Some(PFun)

      case "()" => Some(PUnitType)
      case "[]" => Some(PUnit)

      case _ => None
