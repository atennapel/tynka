package core

import common.Common.*
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty
  type DataEntry = (List[Name], Map[Name, List[Tm]])
  type ConEntry = (Name, List[Tm])
  private val datamap: mutable.Map[Name, DataEntry] =
    mutable.Map.empty
  private val conmap: mutable.Map[Name, ConEntry] = mutable.Map.empty

  case class GlobalEntry(
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

  def setGlobalData(
      name: Name,
      ps: List[Name],
      data: List[(Name, List[Tm])]
  ): Unit =
    datamap += name -> (ps, data.toMap)
    data.foreach((c, ts) => conmap += c -> (name, ts))
  def getGlobalData(name: Name): Option[DataEntry] = datamap.get(name)
  def getGlobalCon(name: Name): Option[ConEntry] = conmap.get(name)

  def resetGlobals(): Unit =
    map.clear()
    datamap.clear()
    conmap.clear()
