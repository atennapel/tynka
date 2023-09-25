package surface

import common.Common.*
import Syntax.*

import parsley.Parsley, Parsley.*
import scala.language.implicitConversions

object Parser:
  object LangLexer:
    import parsley.token.{LanguageDef, Lexer, Predicate, Parser}
    import parsley.character.{alphaNum, isWhitespace, char, oneOf}
    import parsley.combinator.{eof, many}

    private val userOps = "`~!@$%^&*-+=|:/?><,."
    private val userOpsTail = s"$userOps#_;"

    private val lang = LanguageDef.plain.copy(
      commentLine = "--",
      commentStart = "{-",
      commentEnd = "-}",
      nestedComments = true,
      keywords = Set(
        "CV",
        "Val",
        "Comp",
        "def",
        "let",
        "fix",
        "data",
        "con",
        "match",
        "Meta",
        "Ty",
        // "if",
        "then",
        "else",
        "foreign",
        "foreignIO",
        "mutable",
        "do",
        "opaque",
        "unfold",
        "auto"
      ),
      operators = Set(
        "=",
        ":=",
        ":",
        ";",
        "\\",
        ".",
        ",",
        "->",
        "<-",
        "**",
        "_",
        "^",
        "`",
        "$",
        "|"
      ),
      identStart = Predicate(c => c.isLetter || c == '_'),
      identLetter = Predicate(c =>
        c.isLetterOrDigit || c == '_' || c == '\'' || c == '-' || c == '/' || c == ':'
      ),
      opStart = Predicate(userOps.contains(_)),
      opLetter = Predicate(userOpsTail.contains(_)),
      space = Predicate(isWhitespace)
    )
    val lexer = new Lexer(lang)

    def fully[A](p: => Parsley[A]): Parsley[A] = lexer.whiteSpace *> p <* eof

    val ident: Parsley[String] = lexer.identifier
    val userOp: Parsley[String] = lexer.userOp
    val natural: Parsley[Int] = lexer.natural
    val string: Parsley[String] = lexer.stringLiteral

    object Implicits:
      given Conversion[String, Parsley[Unit]] with
        def apply(s: String): Parsley[Unit] =
          if lang.keywords(s) then lexer.keyword(s)
          else if lang.operators(s) then lexer.maxOp(s)
          else void(lexer.symbol_(s))

  object TmParser:
    import parsley.expr.{precedence, Ops, InfixL, InfixR, Prefix, Postfix}
    import parsley.combinator.{many, some, option, sepEndBy, sepBy}
    import parsley.Parsley.pos

    import LangLexer.{ident as ident0, userOp as userOp0, natural, string}
    import LangLexer.Implicits.given

    private def positioned(p: => Parsley[Tm]): Parsley[Tm] =
      (pos <~> p).map(Pos.apply)

    private lazy val ident: Parsley[Name] = ident0.map(Name.apply)
    private lazy val userOp: Parsley[Name] = userOp0.map(Name.apply)
    private lazy val identOrOp: Parsley[Name] = ("(" *> userOp <* ")") <|> ident

    private lazy val bind: Parsley[Bind] =
      "_" #> DontBind <|> identOrOp.map(DoBind.apply)

    private lazy val holeP: Parsley[Tm] =
      ident.flatMap(x0 => {
        val x = x0.expose
        if x.head == '_' then
          pure(Hole(if x.size > 1 then Some(Name(x.tail)) else None))
        else empty
      })

    private lazy val atom: Parsley[Tm] = positioned(
      ("^" *> projAtom).map(Lift.apply)
        <|> ("`" *> projAtom).map(Quote.apply)
        <|> ("$" *> projAtom).map(Splice.apply)
        <|> attempt("(" *> userOp.map(x => Var(x)) <* ")")
        <|> ("(" *> tm <* ")")
        <|> attempt(holeP)
        <|> nat
        <|> ("Meta" #> U1)
        <|> ("Ty" *> projAtom).map(cv => U0(cv))
        <|> ("CV" #> CV)
        <|> ("Comp" #> Comp)
        <|> ("Val" #> Val)
        <|> ident.map(x => Var(x))
    )

    private val unittype = Var(Name("Unit"))
    private val hole = Hole(None)
    private val nZ = Var(Name("Z"))
    private val nS = Var(Name("S"))

    private lazy val nat: Parsley[Tm] =
      natural.map { i =>
        var c = nZ
        for (_ <- 0 until i) c = App(nS, c, ArgIcit(Expl))
        c
      }

    lazy val tm: Parsley[Tm] = positioned(
      attempt(
        piSigma
      ) <|> let <|> lam <|> doP <|>
        precedence[Tm](app)(
          Ops(InfixR)("->" #> ((l, r) => Pi(DontBind, Expl, l, r)))
        )
    )

    private type PiSigmaParam = (List[Bind], Icit, Option[Ty])
    private lazy val piSigmaParam: Parsley[PiSigmaParam] =
      ("{" *> some(bind) <~> option(
        ":" *> tm
      ) <* "}").map { case (xs, ty) => (xs, Impl, ty) }
        <|> attempt("(" *> some(bind) <~> ":" *> tm <* ")")
          .map { case (xs, ty) =>
            (xs, Expl, Some(ty))
          }
        <|> ("(" <~> ")").map(_ => (List(DontBind), Expl, Some(unittype)))

    private lazy val piSigma: Parsley[Tm] =
      ((some(piSigmaParam) <|> app.map(t =>
        List((List(DontBind), Expl, Some(t)))
      )) <~> ("->" #> false <|> "**" #> true) <~> tm)
        .map { case ((ps, isSigma), rt) =>
          ps.foldRight(rt) { case ((xs, i, ty), rt) =>
            xs.foldRight(rt)((x, rt) => Pi(x, i, ty.getOrElse(hole), rt))
          }
        }

    private type DefParam = (List[Bind], Icit, Option[Ty])
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => (List(x), Expl, None))

    private lazy val let: Parsley[Tm] =
      positioned(
        ("let" *> identOrOp <~> many(
          defParam
        ) <~> option(
          ":" *> tm
        ) <~> (":=" #> false <|> "=" #> true) <~> tm <~> ";" *> tm)
          .map { case (((((x, ps), ty), m), v), b) =>
            Let(
              x,
              m,
              ty.map(typeFromParams(m, ps, _)),
              lamFromDefParams(ps, v, ty.isEmpty),
              b
            )
          }
      )

    private enum DoEntry:
      case DoBind(pos: PosInfo, x: Bind, t: Option[Ty], v: Tm)
      case DoLet(
          pos: PosInfo,
          x: Name,
          m: Boolean,
          t: Option[Ty],
          v: Tm
      )
      case DoTm(t: Tm)
    import DoEntry.*
    private val bindVar = Var(Name(">>="))
    private lazy val doP: Parsley[Tm] =
      positioned(
        ("do" *> option("{" *> identOrOp <* "}") <~> many(
          attempt(doEntry)
        ) <~> tm)
          .map { case ((monad, es), b) =>
            val body = es.foldRight(b) {
              // (>>=) {_} {t} v (\x. b)
              case (DoBind(p, x, Some(t), v), b) =>
                Pos(
                  p,
                  App(
                    App(
                      App(
                        App(bindVar, Hole(None), ArgIcit(Impl)),
                        t,
                        ArgIcit(Impl)
                      ),
                      v,
                      ArgIcit(Expl)
                    ),
                    Lam(x, ArgIcit(Expl), None, b),
                    ArgIcit(Expl)
                  )
                )
              // (>>=) v (\x. b)
              case (DoBind(p, x, None, v), b) =>
                Pos(
                  p,
                  App(
                    App(
                      bindVar,
                      v,
                      ArgIcit(Expl)
                    ),
                    Lam(x, ArgIcit(Expl), None, b),
                    ArgIcit(Expl)
                  )
                )
              case (DoLet(p, x, m, t, v), b) =>
                Pos(p, Let(x, m, t, v, b))
              // (>>=) v (\_. b)
              case (DoTm(v), b) =>
                App(
                  App(
                    bindVar,
                    v,
                    ArgIcit(Expl)
                  ),
                  Lam(DontBind, ArgIcit(Expl), None, b),
                  ArgIcit(Expl)
                )
            }
            monad match
              case None => body
              case Some(m) =>
                Let(Name(">>="), true, None, Var(m), body)
          }
      )
    private lazy val doEntry: Parsley[DoEntry] =
      attempt(pos <~> bind <~> option(":" *> tm) <~> "<-" *> tm <* ";").map {
        case (((pos, x), t), v) =>
          DoBind(pos, x, t, v)
      } <|>
        attempt(
          pos <~> "let" *> identOrOp <~> (
            ":=" #> false <|> "=" #> true
          ) <~> option(
            ":" *> tm
          ) <~> tm <* ";"
        )
          .map { case ((((pos, x), m), t), v) =>
            DoLet(pos, x, m, t, v)
          } <|> (tm <* ";").map(DoTm.apply)

    private type LamParam = (List[Bind], ArgInfo, Option[Ty])
    private lazy val lamParam: Parsley[LamParam] =
      attempt(
        "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
      ).map { case ((xs, ty), y) => (xs, ArgNamed(y), ty) }
        <|> attempt(piSigmaParam).map((xs, i, ty) => (xs, ArgIcit(i), ty))
        <|> bind.map(x => (List(x), ArgIcit(Expl), None))

    private lazy val lam: Parsley[Tm] =
      positioned(("\\" *> many(lamParam) <~> "." *> tm).map(lamFromLamParams _))

    private lazy val app: Parsley[Tm] =
      precedence[Tm](appAtom <|> lam)(
        ops(
          "`@#?,.",
          "*/%",
          "+-",
          ":",
          "=!",
          "<>",
          "&",
          "^",
          "|",
          "$",
          "~"
        )*
      )

    private lazy val appAtom: Parsley[Tm] = positioned(
      (projAtom <~> many(arg) <~> option(lam <|> doP))
        .map { case ((fn, args), opt) =>
          (args.flatten ++ opt.map(t => (t, ArgIcit(Expl))))
            .foldLeft(fn) { case (fn, (arg, i)) => App(fn, arg, i) }
        }
    )

    private type Arg = (Tm, ArgInfo)
    private lazy val arg: Parsley[List[Arg]] =
      attempt("{" *> some(identOrOp) <~> "=" *> tm <* "}").map((xs, t) =>
        xs.map(x => (t, ArgNamed(x)))
      )
        <|> ("{" *> tm <* "}").map(t => List((t, ArgIcit(Impl))))
        <|> projAtom.map(t => List((t, ArgIcit(Expl))))

    private lazy val projAtom: Parsley[Tm] = atom

    private def typeFromParams(meta: Boolean, ps: List[DefParam], rt: Ty): Ty =
      ps.foldRight(rt) { case ((xs, i, ty), b) =>
        xs.foldRight(b)((x, b) =>
          Pi(if meta then x else DontBind, i, ty.getOrElse(hole), b)
        )
      }

    private def lamFromDefParams(
        ps: List[DefParam],
        b: Tm,
        useTypes: Boolean
    ): Tm =
      ps.foldRight(b) { case ((xs, i, ty), b) =>
        xs.foldRight(b)(
          Lam(
            _,
            ArgIcit(i),
            if useTypes then Some(ty.getOrElse(hole)) else None,
            _
          )
        )
      }

    private def lamFromLamParams(ps: List[LamParam], b: Tm): Tm =
      ps.foldRight(b) { case ((xs, i, ty), b) =>
        xs.foldRight(b)(Lam(_, i, ty, _))
      }

    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))

    private def opL(o: String): Parsley[InfixL.Op[Tm]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) => App(App(Var(Name(op)), l, ArgIcit(Expl)), r, ArgIcit(Expl))
      )

    private def opR(o: String): Parsley[InfixR.Op[Tm]] =
      attempt(userOpStart(o)).map(op =>
        (l, r) => App(App(Var(Name(op)), l, ArgIcit(Expl)), r, ArgIcit(Expl))
      )

    private def opP(o: String): Parsley[Prefix.Op[Tm]] =
      attempt(userOpStart(o)).map(op =>
        t => App(Var(Name(op)), t, ArgIcit(Expl))
      )

    private def opLevel(s: String): List[Ops[Tm, Tm]] =
      val chars = s.toList
      List(
        Ops(Prefix)(chars.map(c => opP(c.toString))*),
        Ops(InfixL)(chars.map(c => opL(c.toString))*),
        Ops(InfixR)(chars.map(c => opR(c.toString))*)
      )

    private def ops(ss: String*): List[Ops[Tm, Tm]] = ss.flatMap(opLevel).toList

    // definitions
    lazy val defs: Parsley[Defs] = many(defP).map(Defs.apply)

    private lazy val defP: Parsley[Def] =
      (pos <~> "def" *> identOrOp <~> many(
        defParam
      ) <~> option(
        ":" *> tm
      ) <~> (":=" #> false <|> "=" #> true) <~> tm)
        .map { case (((((pos, x), ps), ty), m), v) =>
          DDef(
            pos,
            x,
            m,
            ty.map(typeFromParams(m, ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty)
          )
        }

  lazy val parser: Parsley[Tm] = LangLexer.fully(TmParser.tm)
  lazy val defsParser: Parsley[Defs] = LangLexer.fully(TmParser.defs)
