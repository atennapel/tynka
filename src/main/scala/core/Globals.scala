package core

import common.Common.Name
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty

  case class GlobalEntry(name: Name, tm: Tm, ty: Ty, value: Val, vty: VTy)

  def addGlobal(x: Name, entry: GlobalEntry): Unit = map.put(x, entry)
  def getGlobal(x: Name): Option[GlobalEntry] = map.get(x)

  def resetGlobals(): Unit = map.clear()
