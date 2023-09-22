package core

import common.Common.*
import common.Debug.debug
import Value.*

import scala.collection.mutable.ArrayBuffer
import scala.annotation.tailrec

object Metas:
  private var metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty
  private val stack: ArrayBuffer[ArrayBuffer[MetaEntry]] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved(ty: VTy)
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

  def newMeta(ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(ty))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_) => u
    case Solved(_, _)    => impossible()

  def unsolvedMetaType(id: MetaId): VTy = getMetaUnsolved(id).ty

  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_)      => impossible()
    case s @ Solved(_, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val1): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = Solved(v, u.ty)

  def unsolvedMetas(): List[(MetaId, VTy)] =
    metas.zipWithIndex.collect { case (Unsolved(ty), ix) =>
      (metaId(ix), ty)
    }.toList

  def isUnsolved(id: MetaId): Boolean = getMeta(id) match
    case Unsolved(ty)      => true
    case Solved(value, ty) => false

  def resetMetas(): Unit = metas.clear(); stack.clear()
