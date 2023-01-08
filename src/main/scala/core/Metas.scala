package core

import common.Common.*
import Value.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved(ty: VTy, stage: Stage[VTy])
    case Solved(value: Val, ty: VTy, stage: Stage[VTy])
  export MetaEntry.*

  def freshMeta(ty: VTy, stage: Stage[VTy]): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(ty, stage))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_, _) => u
    case Solved(_, _, _)    => impossible()

  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_, _)      => impossible()
    case s @ Solved(_, _, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = Solved(v, u.ty, u.stage)

  def unsolvedMetas(): List[(MetaId, VTy, Stage[VTy])] =
    metas.zipWithIndex.collect { case (Unsolved(ty, s), ix) =>
      (metaId(ix), ty, s)
    }.toList

  def resetMetas(): Unit = metas.clear()
