package core

import common.Common.*
import common.Debug.debug
import Value.*
import Syntax.Ty

import scala.collection.mutable.ArrayBuffer
import scala.annotation.tailrec

object Metas:
  private var metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty
  private val stack: ArrayBuffer[ArrayBuffer[MetaEntry]] = ArrayBuffer.empty

  enum MetaEntry:
    case Unsolved(deps: Set[MetaId], ty: VTy, cty: Ty, stage: VStage)
    case Solved(deps: Set[MetaId], value: Val, ty: VTy, stage: VStage)
  export MetaEntry.*

  def pushMetas(): Unit =
    stack += metas
    metas = metas.clone()

  def useMetas(): Unit =
    stack.dropRightInPlace(1)

  def discardMetas(): Unit =
    metas = stack.last
    stack.dropRightInPlace(1)

  def freshMeta(ty: VTy, cty: Ty, stage: VStage): MetaId =
    val id = metaId(metas.size)
    metas.addOne(Unsolved(cty.metas, ty, cty, stage))
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_, _, _, _) => u
    case Solved(_, _, _, _)       => impossible()

  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_, _, _, _)   => impossible()
    case s @ Solved(_, _, _, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val, deps: Set[MetaId]): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = Solved(deps, v, u.ty, u.stage)

  def unsolvedMetas(): List[(MetaId, VTy, VStage)] =
    metas.zipWithIndex.collect { case (Unsolved(_, ty, _, s), ix) =>
      (metaId(ix), ty, s)
    }.toList

  def isUnsolved(id: MetaId): Boolean = getMeta(id) match
    case Unsolved(deps, ty, cty, stage) => true
    case Solved(deps, value, ty, stage) => false

  def resetMetas(): Unit = metas.clear()

  // meta ordering
  private def deps(e: MetaEntry): Set[MetaId] = e match
    case Solved(deps, value, ty, stage) => deps
    case Unsolved(deps, ty, cty, stage) => deps

  private def removeDep(m: MetaId, e: MetaEntry): MetaEntry = e match
    case Solved(deps, value, ty, stage) => Solved(deps - m, value, ty, stage)
    case Unsolved(deps, ty, cty, stage) => Unsolved(deps - m, ty, cty, stage)

  private def allNoDeps(ms: ArrayBuffer[MetaEntry]): List[(MetaId, MetaEntry)] =
    ms.toList.zipWithIndex
      .filter((e, _) => deps(e).isEmpty)
      .map((e, i) => (metaId(i), e))

  private def allDependents(
      ms: ArrayBuffer[MetaEntry],
      x: MetaId
  ): List[(MetaId, MetaEntry)] =
    ms.toList.zipWithIndex
      .filter((e, i) => deps(e).contains(x))
      .map((e, i) => (metaId(i), e))

  private def toposort(
      ms: ArrayBuffer[MetaEntry]
  ): Either[List[MetaId], List[MetaId]] =
    @tailrec
    def go(
        ms: ArrayBuffer[MetaEntry],
        l: List[MetaId],
        nodeps: List[(MetaId, MetaEntry)]
    ): Either[List[MetaId], List[MetaId]] = nodeps match
      case Nil if !ms.forall(e => deps(e).isEmpty) =>
        Left(
          ms.toList.zipWithIndex
            .filter((e, i) => deps(e).nonEmpty)
            .map((_, i) => metaId(i))
        )
      case Nil => Right(l)
      case (x, e) :: s =>
        val dependents =
          allDependents(ms, x).map((i, e) => (i, removeDep(x, e)))
        val ms2 = dependents.foldRight(ms.clone()) { case ((x, e), ms) =>
          ms(x.expose) = e
          ms
        }
        go(ms2, x :: l, s ++ dependents.filter((i, e) => deps(e).isEmpty))
    go(ms, Nil, allNoDeps(ms)).map(_.reverse)

  def orderMetas: List[MetaId] =
    toposort(metas) match
      case Left(cycle) =>
        debug(s"cycle in metas: ${cycle.mkString(", ")}")
        impossible()
      case Right(order) => order

  def orderUnsolvedMetas: List[MetaId] = orderMetas.filter(isUnsolved)
