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
        "def",
        "let",
        "if",
        "then",
        "else",
        "Meta",
        "Ty",
        "tcon",
        "con",
        "case",
        "fix",
        "data",
        "import",
        "export",
        "foreign",
        "VF",
        "Val",
        "Fun"
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
      ("^" *> atom).map(Lift.apply)
        <|> ("`" *> atom).map(Quote.apply)
        <|> ("$" *> atom).map(Splice.apply)
        <|> attempt("(" *> userOp.map(Var.apply) <* ")")
        <|> ("(" *> tm <* ")")
        <|> attempt(holeP)
        <|> ("Meta" #> U(SMeta))
        <|> ("Ty" *> atom).map(vf => U(STy(vf)))
        <|> ("VF" #> VF)
        <|> ("Val" #> VFVal)
        <|> ("Fun" #> VFFun)
        <|> ident.map(Var.apply)
    )

    private val unittype = Var(Name("Unit"))
    private val unit = Var(Name("()"))
    private val hole = Hole(None)

    lazy val tm: Parsley[Tm] = positioned(
      attempt(
        piSigma
      ) <|> let <|> lam <|> fix <|>
        precedence[Tm](app)(
          Ops(InfixR)("->" #> ((l, r) => Pi(DontBind, Expl, l, r)))
        )
    )

    private type PiSigmaParam = (List[Bind], Icit, Option[Ty])
    private lazy val piSigmaParam: Parsley[PiSigmaParam] =
      ("{" *> some(bind) <~> option(":" *> tm) <* "}").map((xs, ty) =>
        (xs, Impl, ty)
      )
        <|> attempt("(" *> some(bind) <~> ":" *> tm <* ")").map((xs, ty) =>
          (xs, Expl, Some(ty))
        )
        <|> ("(" <~> ")").map(_ => (List(DontBind), Expl, Some(unittype)))

    private lazy val piSigma: Parsley[Tm] =
      ((some(piSigmaParam) <|> app.map(t =>
        List((List(DontBind), Expl, Some(t)))
      )) <~> "->" *> tm)
        .map { case (ps, rt) =>
          ps.foldRight(rt) { case ((xs, i, ty), rt) =>
            xs.foldRight(rt)((x, rt) => Pi(x, i, ty.getOrElse(hole), rt))
          }
        }

    private lazy val fix: Parsley[Tm] = positioned(
      ("fix" *> "(" *> bind <~> bind <~> "." *> tm <* ")" <~> atom <~> many(
        arg
      ) <~> option(lam)).map { case (((((g, x), b), arg), args), opt) =>
        val fn = Fix(g, x, b, arg)
        (args.flatten ++ opt.map(t => (t, ArgIcit(Expl))))
          .foldLeft(fn) { case (fn, (arg, i)) => App(fn, arg, i) }
      }
    )

    private type DefParam = (List[Bind], Icit, Option[Ty])
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => (List(x), Expl, None))

    private lazy val let: Parsley[Tm] =
      positioned(
        ("let" *> identOrOp <~> many(defParam) <~> option(
          ":" *> tm
        ) <~> (":=" #> false <|> "=" #> true) <~> tm <~> ";" *> tm)
          .map { case (((((x, ps), ty), m), v), b) =>
            Let(
              x,
              m,
              ty.map(typeFromParams(ps, _)),
              lamFromDefParams(ps, v, ty.isEmpty),
              b
            )
          }
      )

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
      (atom <~> many(arg) <~> option(lam))
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
        <|> atom.map(t => List((t, ArgIcit(Expl))))

    private def typeFromParams(ps: List[DefParam], rt: Ty): Ty =
      ps.foldRight(rt) { case ((xs, i, ty), b) =>
        xs.foldRight(b)(Pi(_, i, ty.getOrElse(hole), _))
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

    private def ops(ss: String*): Seq[Ops[Tm, Tm]] = ss.flatMap(opLevel)

    // definitions
    lazy val defs: Parsley[Defs] =
      many(defP <|> dataP <|> includeP).map(Defs.apply)

    private lazy val defP: Parsley[Def] =
      (pos <~> "def" *> identOrOp <~> many(defParam) <~> option(
        ":" *> tm
      ) <~> (":=" #> false <|> "=" #> true) <~> tm)
        .map { case (((((pos, x), ps), ty), m), v) =>
          DDef(
            pos,
            x,
            m,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty)
          )
        }

    private lazy val dataP: Parsley[Def] =
      (pos <~> "data" *> identOrOp <~> many(identOrOp) <~> "=" *> sepBy(
        identOrOp <~> many(atom),
        "|"
      ))
        .map { case (((pos, x), ps), cs) =>
          DData(pos, x, ps, cs)
        }

    private lazy val includeP: Parsley[Def] =
      (pos <~> ("import" #> false <|> "export" #> true) <~> string <~> option(
        "(" *> ("..." #> Left(()) <|> sepEndBy(identOrOp, ",")
          .map(Right.apply)) <* ")"
      )).map {
        case (((pos, exp), m), None) => DImport(pos, exp, m, false, Nil)
        case (((pos, exp), m), Some(Left(_))) => DImport(pos, exp, m, true, Nil)
        case (((pos, exp), m), Some(Right(xs))) =>
          DImport(pos, exp, m, false, xs)
      }

  lazy val parser: Parsley[Tm] = LangLexer.fully(TmParser.tm)
  lazy val defsParser: Parsley[Defs] = LangLexer.fully(TmParser.defs)
