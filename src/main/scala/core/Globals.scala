package core

import common.Common.*
import Syntax.*
import Value.*

import scala.collection.mutable

object Globals:
  private val globals: mutable.ArrayBuffer[GlobalEntry] =
    mutable.ArrayBuffer.empty

  enum GlobalEntry:
    case GlobalEntry0(
        _name: Name,
        tm: Tm0,
        ty: Ty,
        cv: CV,
        value: Val0,
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
    case GlobalData0(
        _name: Name,
        params: List[(Icit, Bind, Ty)],
        levity: Ty,
        cons: List[Name]
    )
    case GlobalCon0(
        _name: Name,
        data: Name,
        params: List[(Bind, Ty, Ty)]
    )
    def name: Name = this match
      case GlobalEntry0(_name, _, _, _, _, _, _) => _name
      case GlobalEntry1(_name, _, _, _, _)       => _name
      case GlobalData0(_name, _, _, _)           => _name
      case GlobalCon0(_name, _, _)               => _name
  export GlobalEntry.*

  def setGlobal(entry: GlobalEntry): Unit = globals += entry
  def getGlobal(x: Name): Option[GlobalEntry] =
    globals.findLast(e => e.name == x)

  def getGlobalData0(x: Name): GlobalData0 = getGlobal(x) match
    case Some(e @ GlobalData0(_, _, _, _)) => e
    case _                                 => impossible()

  def getGlobalCon0(x: Name): GlobalCon0 = getGlobal(x) match
    case Some(e @ GlobalCon0(_, _, _)) => e
    case _                             => impossible()

  def resetGlobals(): Unit = globals.clear()

  def allGlobals: List[GlobalEntry] = globals.toList
