package core

import common.Common.*
import Value.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved(ty: VTy)
    case Solved(value: Val, ty: VTy)
  export MetaEntry.*

  def freshMeta(ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(ty))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_) => u
    case Solved(_, _)    => impossible()

  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_)      => impossible()
    case s @ Solved(_, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val): Unit =
    val ty = getMetaUnsolved(id).ty
    metas(id.expose) = Solved(v, ty)

  def unsolvedMetas(): List[(MetaId, VTy)] = metas.zipWithIndex.collect {
    case (Unsolved(ty), ix) => (metaId(ix), ty)
  }.toList

  def resetMetas(): Unit = metas.clear()
