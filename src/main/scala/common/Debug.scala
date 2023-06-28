package common

object Debug:
  private var status: Boolean = false

  def isDebug: Boolean = status

  def setDebug(newStatus: Boolean): Unit =
    status = newStatus

  def debug(msg: => Any): Unit = if status then println(msg)
