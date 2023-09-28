package core

import common.Common.*
import common.Debug.debug
import Value.*
import Syntax.Tm1
import Ctx as Ctx
import surface.Syntax as S

import scala.collection.mutable.ArrayBuffer
import scala.annotation.tailrec

object Metas:
  private var metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty
  private val stack: ArrayBuffer[ArrayBuffer[MetaEntry]] = ArrayBuffer.empty

  type Blocking = Set[Int]

  enum MetaEntry:
    case Unsolved(blocking: Blocking, ty: VTy)
    case Solved(value: Val1, ty: VTy)
  export MetaEntry.*

  def pushMetas(): Unit =
    stack += metas
    metas = metas.clone()

  def useMetas(): Unit =
    stack.dropRightInPlace(1)

  def discardMetas(): Unit =
    metas = stack.last
    stack.dropRightInPlace(1)

  def newMeta(blocking: Blocking, ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(blocking, ty))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_, _) => u
    case Solved(_, _)       => impossible()

  def unsolvedMetaType(id: MetaId): VTy = getMetaUnsolved(id).ty

  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_, _)   => impossible()
    case s @ Solved(_, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val1): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = Solved(v, u.ty)

  def getMetas(): List[(MetaId, VTy, Option[Val1])] =
    metas.zipWithIndex.collect {
      case (Solved(v, ty), ix)   => (metaId(ix), ty, Some(v))
      case (Unsolved(_, ty), ix) => (metaId(ix), ty, None)
    }.toList

  def unsolvedMetas(): List[(MetaId, VTy)] =
    metas.zipWithIndex.collect { case (Unsolved(_, ty), ix) =>
      (metaId(ix), ty)
    }.toList

  def isUnsolved(id: MetaId): Boolean = getMeta(id) match
    case Unsolved(_, ty)   => true
    case Solved(value, ty) => false

  // postponing
  private var postponed: ArrayBuffer[PostponedEntry] = ArrayBuffer.empty
  private val postponedStack: ArrayBuffer[ArrayBuffer[PostponedEntry]] =
    ArrayBuffer.empty

  inline def nextPostponedId: PostponedId = postponedId(postponed.size)

  enum PostponedEntry:
    case PECheck1(ctx: Ctx, tm: S.Tm, ty: VTy, id: MetaId)
    case PECheckVarU1(ctx: Ctx, x: Name, ty: VTy, id: MetaId)
    case PECheck1Done(ctx: Ctx, tm: Option[Tm1])
  export PostponedEntry.*

  def pushPostponed(): Unit =
    postponedStack += postponed
    postponed = postponed.clone()

  def usePostponed(): Unit =
    postponedStack.dropRightInPlace(1)

  def discardPostponed(): Unit =
    postponed = postponedStack.last
    postponedStack.dropRightInPlace(1)

  def newPostponed(entry: PostponedEntry): PostponedId =
    val id = nextPostponedId
    postponed.addOne(entry)
    id

  def getPostponed(id: PostponedId): PostponedEntry = postponed(id.expose)

  def modifyPostponed(id: PostponedId)(
      fn: PostponedEntry => PostponedEntry
  ): Unit =
    postponed(id.expose) = fn(postponed(id.expose))

  def setPostponed(id: PostponedId, entry: PostponedEntry): Unit =
    postponed(id.expose) = entry

  def addBlocking(blocked: PostponedId, blocks: MetaId): Unit =
    modifyMeta(blocks) {
      case Unsolved(bs, ty) => Unsolved(bs + blocked.expose, ty)
      case _                => impossible()
    }

  def getAllPostponed(): List[(PostponedId, PostponedEntry)] =
    postponed.zipWithIndex.map((e, i) => (postponedId(i), e)).toList

  //
  def resetMetas(): Unit =
    metas.clear()
    stack.clear()
    postponed.clear()
    postponedStack.clear()
