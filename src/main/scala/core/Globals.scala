package core

import common.Common.Name
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty

  case class GlobalEntry(
      name: Name,
      tm: Tm,
      ty: Ty,
      univ: Univ,
      value: Val,
      vty: VTy,
      vuniv: VUniv
  )

  def setGlobal(entry: GlobalEntry): Unit = map.put(entry.name, entry)
  def getGlobal(x: Name): Option[GlobalEntry] = map.get(x)

  def resetGlobals(): Unit = map.clear()
