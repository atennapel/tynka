package core

import common.Common.*
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty

  case class GlobalEntry(
      opaque: Boolean,
      name: Name,
      tm: Tm,
      ty: Ty,
      stage: CStage,
      value: Val,
      vty: VTy,
      vstage: VStage
  )

  def setGlobal(entry: GlobalEntry): Unit =
    map.put(entry.name, entry)
  def getGlobal(x: Name): Option[GlobalEntry] = map.get(x)

  def resetGlobals(): Unit =
    map.clear()
