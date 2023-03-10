package common

// mutable reference
final case class Ref[T](var value: T):
  def set(x: T): Ref[T] =
    value = x
    this

  def update(f: T => T): Ref[T] =
    value = f(value)
    this

  def setGetPrevious(x: T): T =
    val cache = value
    value = x
    cache

  def updateGetPrevious(f: T => T): T =
    val cache = value
    value = f(value)
    cache
