package core

import common.Common.*
import Value.*

import scala.collection.mutable.ArrayBuffer

object Metas:
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved(ty: VTy, stage: VStage)
    case Solved(value: Val, ty: VTy, stage: VStage)
  export MetaEntry.*

  def freshMeta(ty: VTy, stage: VStage): MetaId =
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

  def unsolvedMetas(): List[(MetaId, VTy, VStage)] =
    metas.zipWithIndex.collect { case (Unsolved(ty, s), ix) =>
      (metaId(ix), ty, s)
    }.toList

  def resetMetas(): Unit = metas.clear()
