package core

import common.Common.*
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[(String, Name), GlobalEntry] = mutable.Map.empty

  case class GlobalEntry(
      auto: Boolean,
      opaque: Boolean,
      module: String,
      name: Name,
      tm: Tm,
      ty: Ty,
      stage: CStage,
      value: Val,
      vty: VTy,
      vstage: VStage
  )

  def setGlobal(entry: GlobalEntry): Unit =
    map.put((entry.module, entry.name), entry)
  def getGlobal(m: String, x: Name): Option[GlobalEntry] = map.get((m, x))

  def resetGlobals(): Unit =
    map.clear()

  def allEntriesFromModule(m: String): List[GlobalEntry] =
    map.values.filter(e => e.module == m).toList

  def allNamesFromModule(m: String): List[Name] =
    allEntriesFromModule(m).map(_.name).toList

  def allGlobals: Map[(String, Name), GlobalEntry] = map.toMap
