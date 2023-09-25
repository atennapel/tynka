package core

import common.Common.*
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val map: mutable.Map[Name, GlobalEntry] = mutable.Map.empty

  enum GlobalEntry:
    case GlobalEntry0(
        _name: Name,
        tm: Tm0,
        ty: Ty,
        value: Val0,
        cv: CV,
        vty: VTy,
        vcv: VCV
    )
    case GlobalEntry1(
        _name: Name,
        tm: Tm1,
        ty: Ty,
        value: Val1,
        vty: VTy
    )
    def name: Name = this match
      case GlobalEntry0(_name, _, _, _, _, _, _) => _name
      case GlobalEntry1(_name, _, _, _, _)       => _name
  export GlobalEntry.*

  def setGlobal(entry: GlobalEntry): Unit = map.put(entry.name, entry)
  def getGlobal(x: Name): Option[GlobalEntry] = map.get(x)

  def resetGlobals(): Unit = map.clear()

  def allGlobals: Map[Name, GlobalEntry] = map.toMap
