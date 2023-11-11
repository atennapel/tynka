package common

import scala.annotation.{targetName, unused}
import scala.collection.mutable

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
    inline def -(o: Int): Ix = i - o

  // levels
  opaque type Lvl = Int
  inline def lvl0: Lvl = 0
  inline def mkLvl(i: Int): Lvl = i
  extension (l: Lvl)
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    @targetName("subLvl")
    inline def -(o: Int): Lvl = l - o
    inline def <(o: Lvl): Boolean = l < o
    @targetName("exposeLvl")
    inline def expose: Int = l
    inline def toIx(implicit k: Lvl): Ix = k - l - 1

  // names
  case class Name(x: String):
    override def toString: String =
      if !isOperator || (x.head == '(' || x.head == '[') then x else s"($x)"
    def isOperator: Boolean = !x.head.isLetter && x.head != '_'
    def expose: String = x
    def toBind: Bind = DoBind(this)

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
  enum PruneEntry:
    case PESkip
    case PEBind0
    case PEBind1(icit: Icit)
  export PruneEntry.*
  type Pruning = List[PruneEntry]

  opaque type RevPruning = Pruning
  extension (r: RevPruning)
    @targetName("exposeRevPruning")
    inline def expose: Pruning = r
  object RevPruning:
    inline def apply(p: Pruning): RevPruning = p.reverse

  // meta ids
  opaque type MetaId = Int
  inline def metaId(id: Int): MetaId = id
  extension (id: MetaId)
    @targetName("exposeMetaId")
    inline def expose: Int = id

  // postponed ids
  opaque type PostponedId = Int
  inline def postponedId(id: Int): PostponedId = id
  extension (id: PostponedId)
    @targetName("exposePostponedId")
    inline def expose: Int = id
    @targetName("addPostponedId")
    inline def +(o: Int): PostponedId = id + o
    @targetName("ltPostponedId")
    inline def <(o: PostponedId): Boolean = id < o
