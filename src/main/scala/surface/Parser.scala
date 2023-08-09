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
        "fix",
        "data",
        "match",
        "Meta",
        "Ty",
        "if",
        "then",
        "else",
        "foreign",
        "foreignIO",
        "mutable",
        "do",
        "opaque",
        "unfold"
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
        <|> string.map(StringLit.apply)
        <|> attempt("(" *> userOp.map(x => Var(x)) <* ")")
        <|> ("(" *> sepEndBy(tm, ",").map(mkPair) <* ")")
        <|> (option("#").map(_.isDefined) <~> "[" *> sepEndBy(tm, ",") <* "]")
          .map(mkUnitPair)
        <|> attempt(holeP)
        <|> nat
        <|> ("Meta" #> U(SMeta))
        <|> ("Ty" *> projAtom).map(cv => U(STy(cv)))
        <|> ident.map(x => Var(x))
    )

    private val unittype = Var(Name("()"))
    private val unit = Var(Name("[]"))
    private val hole = Hole(None)
    private val nZ = Var(Name("Z"))
    private val nS = Var(Name("S"))

    private lazy val nat: Parsley[Tm] = natural.map(IntLit.apply)
    /*natural.map { i =>
      var c = nZ
      for (_ <- 0 until i) c = App(nS, c, ArgIcit(Expl))
      c
    }*/

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

    lazy val tm: Parsley[Tm] = positioned(
      attempt(
        piSigma
      ) <|> let <|> lam <|> ifP <|> fix <|> matchP <|> foreignP <|> doP <|> unfoldP <|>
        precedence[Tm](app)(
          Ops(InfixR)("**" #> ((l, r) => Sigma(DontBind, l, r))),
          Ops(InfixR)("->" #> ((l, r) => Pi(Many, DontBind, Expl, l, r)))
        )
    )

    private lazy val usage: Parsley[Usage] =
      option(("0" #> Zero) <|> ("1" #> One)).map(o => o.getOrElse(Many))

    private type PiSigmaParam = (Usage, List[Bind], Icit, Option[Ty])
    private lazy val piSigmaParam: Parsley[PiSigmaParam] =
      ("{" *> usage <~> some(bind) <~> option(":" *> tm) <* "}").map {
        case ((u, xs), ty) => (u, xs, Impl, ty)
      }
        <|> attempt("(" *> usage <~> some(bind) <~> ":" *> tm <* ")")
          .map { case ((u, xs), ty) =>
            (u, xs, Expl, Some(ty))
          }
        <|> ("(" <~> ")").map(_ => (Many, List(DontBind), Expl, Some(unittype)))

    private lazy val piSigma: Parsley[Tm] =
      ((some(piSigmaParam) <|> app.map(t =>
        List((Many, List(DontBind), Expl, Some(t)))
      )) <~> ("->" #> false <|> "**" #> true) <~> tm)
        .map { case ((ps, isSigma), rt) =>
          ps.foldRight(rt) { case ((u, xs, i, ty), rt) =>
            xs.foldRight(rt)((x, rt) =>
              if isSigma then Sigma(x, ty.getOrElse(hole), rt)
              else Pi(u, x, i, ty.getOrElse(hole), rt)
            )
          }
        }

    private lazy val fix: Parsley[Tm] = positioned(
      ("fix" *> "(" *> bind <~> bind <~> "." *> tm <* ")" <~> projAtom <~> many(
        arg
      ) <~> option(lam)).map { case (((((g, x), b), arg), args), opt) =>
        val fn = Fix(g, x, b, arg)
        (args.flatten ++ opt.map(t => (t, ArgIcit(Expl))))
          .foldLeft(fn) { case (fn, (arg, i)) => App(fn, arg, i) }
      }
    )

    private lazy val unfoldP: Parsley[Tm] = positioned(
      ("unfold" *> some(identOrOp) <~> ";" *> tm).map(Unfold.apply)
    )

    private lazy val foreignP: Parsley[Tm] = positioned(
      (("foreignIO" #> true <|> "foreign" #> false) <~> projAtom <~> projAtom <~> many(
        projAtom
      ))
        .map { case (((io, rt), l), as) =>
          Foreign(io, rt, l, as)
        }
    )

    private lazy val matchP: Parsley[Tm] = positioned(
      ("match" *> tm <~> many(
        attempt(
          pos <~>
            "|" *> identOrOp.flatMap(x =>
              if x.expose == "_" then empty else pure(x)
            ) <~> option("{" *> identOrOp <* "}") <~> many(bind) <~> "." *> tm
        )
      ) <~> option(pos <~> "|" *> option("_") *> "." *> tm)).map {
        case ((scrut, cs), other) =>
          Match(
            scrut,
            cs.map { case ((((pos, c), cx), ps), b) => (pos, c, cx, ps, b) },
            other
          )
      }
    )

    private type DefParam = (Usage, List[Bind], Icit, Option[Ty])
    private lazy val defParam: Parsley[DefParam] =
      attempt(piSigmaParam) <|> bind.map(x => (Many, List(x), Expl, None))

    private val nConsumeLinearUnit = Var(Name("consumeLinearUnit"))
    private lazy val let: Parsley[Tm] =
      positioned(
        attempt(
          ("let" *> ("(" *> ")") *> "=" *> tm <~> ";" *> tm)
        ).map { case (v, b) =>
          App(App(nConsumeLinearUnit, v, ArgIcit(Expl)), b, ArgIcit(Expl))
        } <|>
          ("let" *> usage <~> identOrOp <~> many(defParam) <~> option(
            ":" *> tm
          ) <~> (":=" #> false <|> "=" #> true) <~> tm <~> ";" *> tm)
            .map { case ((((((u, x), ps), ty), m), v), b) =>
              Let(
                u,
                x,
                m,
                ty.map(typeFromParams(ps, _)),
                lamFromDefParams(ps, v, ty.isEmpty),
                b
              )
            }
      )

    private enum DoEntry:
      case DoBind(pos: PosInfo, x: Bind, t: Option[Ty], v: Tm)
      case DoLet(
          pos: PosInfo,
          usage: Usage,
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
              case (DoLet(p, u, x, m, t, v), b) => Pos(p, Let(u, x, m, t, v, b))
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
                Let(Many, Name(">>="), true, None, Var(m, true), body)
          }
      )
    private lazy val doEntry: Parsley[DoEntry] =
      attempt(pos <~> bind <~> option(":" *> tm) <~> "<-" *> tm <* ";").map {
        case (((pos, x), t), v) =>
          DoBind(pos, x, t, v)
      } <|>
        attempt(
          pos <~> usage <~> "let" *> identOrOp <~> (":=" #> false <|> "=" #> true) <~> option(
            ":" *> tm
          ) <~> tm <* ";"
        )
          .map { case (((((pos, u), x), m), t), v) =>
            DoLet(pos, u, x, m, t, v)
          } <|> (tm <* ";").map(DoTm.apply)

    private type LamParam = (List[Bind], ArgInfo, Option[Ty])
    private lazy val lamParam: Parsley[LamParam] =
      attempt(
        "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
      ).map { case ((xs, ty), y) => (xs, ArgNamed(y), ty) }
        <|> attempt(piSigmaParam).map((_, xs, i, ty) => (xs, ArgIcit(i), ty))
        <|> bind.map(x => (List(x), ArgIcit(Expl), None))

    private lazy val lam: Parsley[Tm] =
      positioned(("\\" *> many(lamParam) <~> "." *> tm).map(lamFromLamParams _))

    private lazy val ifP: Parsley[Tm] =
      positioned(
        ("if" *> tm <~> "then" *> (pos <~> tm) <~> "else" *> (pos <~> tm))
          .map { case ((c, (pt, t)), (pf, f)) =>
            Match(
              c,
              List(
                (pt, Name("True"), None, Nil, t),
                (pf, Name("False"), None, Nil, f)
              ),
              None
            )
          }
      )

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

    private lazy val projAtom: Parsley[Tm] = positioned(
      (atom <~> many(proj)).map((t, ps) => ps.foldLeft(t)(Proj.apply))
    )

    private lazy val proj: Parsley[ProjType] =
      "." *> ("1" #> Fst <|> "2" #> Snd <|> identOrOp.map(Named.apply))

    private def typeFromParams(ps: List[DefParam], rt: Ty): Ty =
      ps.foldRight(rt) { case ((u, xs, i, ty), b) =>
        xs.foldRight(b)(Pi(u, _, i, ty.getOrElse(hole), _))
      }

    private def lamFromDefParams(
        ps: List[DefParam],
        b: Tm,
        useTypes: Boolean
    ): Tm =
      ps.foldRight(b) { case ((u, xs, i, ty), b) =>
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
      many(defP <|> dataP <|> importP).map(Defs.apply)

    private lazy val defP: Parsley[Def] =
      (pos <~> option("opaque") <~> "def" *> identOrOp <~> many(
        defParam
      ) <~> option(
        ":" *> tm
      ) <~> (":=" #> false <|> "=" #> true) <~> tm)
        .map { case ((((((pos, opq), x), ps), ty), m), v) =>
          DDef(
            pos,
            opq.isDefined,
            x,
            m,
            ty.map(typeFromParams(ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty)
          )
        }

    private lazy val dataP: Parsley[Def] =
      (pos <~> "data" *> identOrOp <~> many(
        identOrOp
      ) <~> option(
        (":=" <|> "|") *> sepBy(
          pos <~> identOrOp <~> many(projAtom),
          "|"
        )
      ))
        .map { case (((pos, x), ps), cs) =>
          DData(
            pos,
            x,
            ps,
            cs.map(cs => cs.map { case ((pos, x), ts) => (pos, x, ts) })
              .getOrElse(Nil)
          )
        }

    private lazy val importP: Parsley[Def] =
      (pos <~> "import" *> string).map { case (pos, m) =>
        DImport(pos, m)
      }

  lazy val parser: Parsley[Tm] = LangLexer.fully(TmParser.tm)
  lazy val defsParser: Parsley[Defs] = LangLexer.fully(TmParser.defs)
