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
        "else"
      ),
      operators = Set(
        "=",
        ":",
        ";",
        "\\",
        ".",
        ",",
        "->",
        "**",
        "_",
        "^",
        "`",
        "$"
      ),
      identStart = Predicate(_.isLetter),
      identLetter =
        Predicate(c => c.isLetterOrDigit || c == '_' || c == '\'' || c == '-'),
      opStart = Predicate(userOps.contains(_)),
      opLetter = Predicate(userOpsTail.contains(_)),
      space = Predicate(isWhitespace)
    )
    val lexer = new Lexer(lang)

    def fully[A](p: => Parsley[A]): Parsley[A] = lexer.whiteSpace *> p <* eof

    val ident: Parsley[String] = lexer.identifier
    val userOp: Parsley[String] = lexer.userOp
    val natural: Parsley[Int] = lexer.natural

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

    import LangLexer.{ident as ident0, userOp as userOp0, natural}
    import LangLexer.Implicits.given

    private def positioned(p: => Parsley[Tm]): Parsley[Tm] =
      (pos <~> p).map(Pos.apply)

    private lazy val ident: Parsley[Name] = ident0.map(Name.apply)
    private lazy val userOp: Parsley[Name] = userOp0.map(Name.apply)
    private lazy val identOrOp: Parsley[Name] = ("(" *> userOp <* ")") <|> ident

    private lazy val bind: Parsley[Bind] =
      "_" #> DontBind <|> identOrOp.map(DoBind.apply)

    private lazy val holeP: Parsley[Tm] = ("_" *> option(ident)).map(Hole.apply)

    private lazy val atom: Parsley[Tm] = positioned(
      ("^" *> atom).map(Lift.apply)
        <|> ("`" *> atom).map(Quote.apply)
        <|> ("$" *> atom).map(Splice.apply)
        <|> attempt("(" *> userOp.map(Var.apply) <* ")")
        <|> ("(" *> sepEndBy(tm, ",").map(mkPair) <* ")")
        <|> (option("#").map(_.isDefined) <~> "[" *> sepEndBy(tm, ",") <* "]")
          .map(mkUnitPair)
        <|> holeP
        <|> nat
        <|> ident.map(Var.apply)
    )

    private val unittype = Var(Name("()"))
    private val unit = Var(Name("[]"))
    private val hole = Hole(None)
    private val nZ = Var(Name("Z"))
    private val nS = Var(Name("S"))

    private def mkPair(ts: List[Tm]): Tm = ts match
      case Nil => unittype
      case ts  => ts.reduceRight(Pair.apply)

    private val nil = Var(Name("Nil"))
    private val cons = Var(Name("::"))
    private def mkUnitPair(isList: Boolean, ts: List[Tm]): Tm =
      if isList then
        ts.foldRight(nil)((x, y) =>
          App(App(cons, x, ArgIcit(Expl)), y, ArgIcit(Expl))
        )
      else ts.foldRight(unit)(Pair.apply)

    private lazy val nat: Parsley[Tm] = natural.map(n =>
      var c: Tm = nZ
      for (_ <- 0.until(n)) c = App(nS, c, ArgIcit(Expl))
      c
    )

    lazy val tm: Parsley[Tm] = positioned(
      attempt(piSigma) <|> let <|> lam <|> ifP <|>
        precedence[Tm](app)(
          Ops(InfixR)("**" #> ((l, r) => Sigma(DontBind, l, r))),
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
      )) <~> ("->" #> false <|> "**" #> true) <~> tm)
        .map { case ((ps, isSigma), rt) =>
          ps.foldRight(rt) { case ((xs, i, ty), rt) =>
            xs.foldRight(rt)((x, rt) =>
              if isSigma then Sigma(x, ty.getOrElse(hole), rt)
              else Pi(x, i, ty.getOrElse(hole), rt)
            )
          }
        }

    private type DefParam = (List[Bind], Icit, Option[Ty])
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => (List(x), Expl, None))

    private lazy val let: Parsley[Tm] =
      ("let" *> identOrOp <~> many(defParam) <~> option(
        ":" *> tm
      ) <~> "=" *> tm <~> ";" *> tm)
        .map { case ((((x, ps), ty), v), b) =>
          Let(
            x,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty),
            b
          )
        }

    private type LamParam = (List[Bind], ArgInfo, Option[Ty])
    private lazy val lamParam: Parsley[LamParam] =
      attempt(
        "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
      ).map { case ((xs, ty), y) => (xs, ArgNamed(y), ty) }
        <|> attempt(piSigmaParam).map((xs, i, ty) => (xs, ArgIcit(i), ty))
        <|> bind.map(x => (List(x), ArgIcit(Expl), None))

    private lazy val lam: Parsley[Tm] =
      ("\\" *> many(lamParam) <~> "." *> tm).map(lamFromLamParams _)

    private val elimBoolVar: Tm = Var(Name("elimBool"))
    private val tyName = Name("ty")
    private lazy val ifP: Parsley[Tm] =
      ("if" *> tm <~> option(":" *> tm) <~> "then" *> tm <~> "else" *> tm)
        .map { case (((c, ty), t), f) =>
          ty match
            // elimBool (let t = _; \_. t) t f c
            case None =>
              App(
                App(
                  App(
                    App(
                      elimBoolVar,
                      Let(
                        tyName,
                        None,
                        hole,
                        Lam(DontBind, ArgIcit(Expl), None, Var(tyName))
                      ),
                      ArgIcit(Expl)
                    ),
                    t,
                    ArgIcit(Expl)
                  ),
                  f,
                  ArgIcit(Expl)
                ),
                c,
                ArgIcit(Expl)
              )
            // elimBool ty t f c
            case Some(ty) =>
              App(
                App(
                  App(
                    App(
                      elimBoolVar,
                      ty,
                      ArgIcit(Expl)
                    ),
                    t,
                    ArgIcit(Expl)
                  ),
                  f,
                  ArgIcit(Expl)
                ),
                c,
                ArgIcit(Expl)
              )
        }

    private lazy val app: Parsley[Tm] =
      precedence[Tm](appAtom)(
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
      (projAtom <~> many(arg) <~> option(let <|> lam <|> ifP))
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

    private lazy val projAtom: Parsley[Tm] = positioned(
      (atom <~> many(proj)).map((t, ps) => ps.foldLeft(t)(Proj.apply))
    )

    private lazy val proj: Parsley[ProjType] =
      "." *> ("1" #> Fst <|> "2" #> Snd <|> identOrOp.map(Named.apply))

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
    lazy val defs: Parsley[Defs] = many(defP).map(Defs.apply)

    private lazy val defP: Parsley[Def] =
      ("def" *> identOrOp <~> many(defParam) <~> option(
        ":" *> tm
      ) <~> "=" *> tm)
        .map { case (((x, ps), ty), v) =>
          DDef(
            x,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty)
          )
        }

  lazy val parser: Parsley[Tm] = LangLexer.fully(TmParser.tm)
  lazy val defsParser: Parsley[Defs] = LangLexer.fully(TmParser.defs)
