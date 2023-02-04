package elaboration

import surface.Syntax.Defs
import common.Common.*
import surface.Parser.defsParser
import Elaboration.elaborate
import core.Globals.{GlobalEntry, setGlobal}
import core.Syntax as C
import common.Debug.debug

import parsley.io.given
import java.net.URI
import java.io.File
import scala.io.Source
import scala.collection.mutable
import scala.annotation.tailrec

object ModuleLoading:
  private type DepMap = mutable.Map[String, Entry]
  private val urimap: DepMap = mutable.Map.empty

  private case class Entry(
      uri: String,
      filename: String,
      defs: Defs,
      uris: Set[String]
  ):
    def hasNoDeps: Boolean = uris.isEmpty
    def removeDep(x: String): Entry = Entry(uri, filename, defs, uris - x)

  private def hasScheme(uri: String): Boolean = uri.contains(":")
  private def transformFilename(uri: String): String =
    if hasScheme(uri) then uri
    else if uri.endsWith(".tynka") then s"file:$uri"
    else s"file:$uri.tynka"
  private def transformUri(uri: String): String =
    if hasScheme(uri) then uri
    else if uri.endsWith(".tynka") then uri.take(uri.size - 6)
    else uri

  def load(uri0: String): (String, C.Defs) =
    val uri = transformUri(uri0)
    debug(s"load module start: $uri")
    loadUris(uri)
    toposort(urimap) match
      case Left(cycle) =>
        throw Exception(s"cycle in modules: ${cycle.mkString(", ")}")
      case Right(order) =>
        debug(s"modules to load: $order")
        val eds = C.Defs(order.flatMap(x => loadUri(x).defs))
        (uri, eds)

  private def loadUris(uri: String): Unit =
    if !urimap.contains(uri) then
      debug(s"load uris: $uri")
      val filename = transformFilename(uri)
      val text = Source.fromURL(filename).mkString
      val tm = defsParser
        .parse(text)
        .toTry
        .get
      val (uris, defs) = tm.includes
      urimap.put(uri, Entry(uri, filename, defs, uris.toSet))
      uris.filter(!urimap.contains(_)).foreach(loadUris)

  private def loadUri(uri: String): C.Defs =
    debug(s"load uri: $uri")
    val entry = urimap(uri)
    val eds = elaborate(transformFilename(uri), entry.defs)
    debug(s"loaded uri: $uri")
    eds

  private def toposort(map: DepMap): Either[List[String], List[String]] =
    toposort(map.clone(), Nil, map.values.filter(_.hasNoDeps).toList)
      .map(_.reverse)

  @tailrec
  private def toposort(
      map: DepMap,
      l: List[String],
      es: List[Entry]
  ): Either[List[String], List[String]] = es match
    case Nil if !map.values.forall(_.hasNoDeps) =>
      Left(map.filter((_, v) => !v.hasNoDeps).keys.toList)
    case Nil => Right(l)
    case Entry(x, _, _, deps) :: s =>
      val dependents =
        map.values.filter(_.uris.contains(x)).map(_.removeDep(x))
      dependents.foreach(e => map += (e.uri -> e))
      toposort(map, x :: l, s ++ dependents.filter(_.hasNoDeps))
