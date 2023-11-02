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
        "rec",
        "data",
        "con",
        "match",
        "Meta",
        "Ty",
        "if",
        "then",
        "else",
        "unsafeJVM",
        // "foreignIO",
        // "mutable",
        "do"
        // "opaque",
        // "unfold",
        // "auto"
      ),
      operators = Set(
        "=",
        ":=",
        ":",
        ";",
        "\\",
        // ".",
        "=>",
        ",",
        "->",
        "<-",
        // "**",
        "_",
        "^",
        "`",
        "$",
        "|",
        "@"
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
    val int: Parsley[Int] = lexer.integer

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

    import LangLexer.{ident as ident0, userOp as userOp0, int, string}
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
        <|> attempt(int.map(IntLit.apply))
        <|> string.map(StringLit.apply)
        <|> ("Meta" #> U1)
        <|> ("Ty" *> projAtom).map(cv => U0(cv))
        <|> ("CV" #> CV)
        <|> ("Comp" #> Comp)
        <|> ("Val" #> Val)
        <|> ident.map(x => Var(x))
    )

    private val unittype = Var(Name("Unit"))
    private val hole = Hole(None)

    lazy val tm: Parsley[Tm] = positioned(
      attempt(
        piSigma
      ) <|> let <|> lam <|> doP <|> matchP <|> ifP <|> foreignP <|>
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
        ("let" *> option("rec") <~> identOrOp <~> many(
          defParam
        ) <~> option(
          ":" *> tm
        ) <~> (":=" #> false <|> "=" #> true) <~> tm <~> ";" *> tm)
          .map { case ((((((rec, x), ps), ty), m), v), b) =>
            Let(
              x,
              rec.isDefined,
              m,
              ty.map(typeFromParams(m, ps, _)),
              lamFromDefParams(ps, v, ty.isEmpty),
              b
            )
          }
      )

    private def addPatAs(x: Name, p: Pat): Parsley[Pat] =
      p match
        case PCon(con, DontBind, args) => pure(PCon(con, DoBind(x), args))
        case _                         => empty

    private lazy val patAppP: Parsley[Pat] =
      attempt(
        identOrOp <~> "@" *> (("(" *> patP <* ")") <|> (identOrOp <~> some(
          patAtomP
        )).map((c, args) => PCon(c, DontBind, args)))
      ).flatMap(addPatAs) <|>
        attempt(identOrOp <~> some(patAtomP)).map((c, args) =>
          PCon(c, DontBind, args)
        ) <|> patAtomP

    private lazy val patAtomP: Parsley[Pat] =
      ("(" *> patP <* ")") <|> bind.map(PVar.apply)

    private lazy val patP: Parsley[Pat] =
      precedence[Pat](patAppP)(
        defaultOps(
          (op, t) => PCon(op, DontBind, List(t)),
          (op, l, r) => PCon(op, DontBind, List(l, r))
        )*
      )

    private lazy val clauseP: Parsley[(PosInfo, List[Pat], Option[Tm], Tm)] =
      ("|" *> pos <~> sepBy(patP, ",") <~> option("if" *> tm) <~> "=>" *> tm)
        .map { case (((pos, pats), guard), tm) =>
          (pos, pats, guard, tm)
        }

    private lazy val matchP: Parsley[Tm] = positioned(
      ("match" *> sepBy(tm, ",") <~> many(clauseP)).map(Match.apply)
    )

    private lazy val ifP: Parsley[Tm] =
      positioned(
        ("if" *> tm <~> "then" *> (pos <~> tm) <~> "else" *> (pos <~> tm))
          .map { case ((c, (pt, t)), (pf, f)) =>
            val x = Name("b")
            Match(
              List(Let(x, false, true, Some(Var(Name("Bool"))), c, Var(x))),
              List(
                (pt, List(PCon(Name("True"), DontBind, Nil)), None, t),
                (pf, List(PCon(Name("False"), DontBind, Nil)), None, f)
              )
            )
          }
      )

    private lazy val foreignP: Parsley[Tm] = positioned(
      (("unsafeJVM" #> false <|> "unsafeJVMIO" #> true) <~> projAtom <~> projAtom <~> many(
        projAtom
      ))
        .map { case (((io, rt), l), as) =>
          Foreign(io, rt, l, as)
        }
    )

    private enum DoEntry:
      case DoBind(pos: PosInfo, x: Bind, t: Option[Ty], v: Tm)
      case DoLet(
          pos: PosInfo,
          x: Name,
          rec: Boolean,
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
              case (DoLet(p, x, rec, m, t, v), b) =>
                Pos(p, Let(x, rec, m, t, v, b))
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
                Let(Name(">>="), false, true, None, Var(m, true), body)
          }
      )
    private lazy val doEntry: Parsley[DoEntry] =
      attempt(pos <~> bind <~> option(":" *> tm) <~> "<-" *> tm <* ";").map {
        case (((pos, x), t), v) =>
          DoBind(pos, x, t, v)
      } <|>
        attempt(
          pos <~> "let" *> option("rec") <~> identOrOp <~> (
            ":=" #> false <|> "=" #> true
          ) <~> option(
            ":" *> tm
          ) <~> tm <* ";"
        )
          .map { case (((((pos, rec), x), m), t), v) =>
            DoLet(pos, x, rec.isDefined, m, t, v)
          } <|> (tm <* ";").map(DoTm.apply)

    private type LamParam = (List[Bind], ArgInfo, Option[Ty])
    private lazy val lamParam: Parsley[LamParam] =
      attempt(
        "{" *> some(bind) <~> option(":" *> tm) <~> "=" *> identOrOp <* "}"
      ).map { case ((xs, ty), y) => (xs, ArgNamed(y), ty) }
        <|> attempt(piSigmaParam).map((xs, i, ty) => (xs, ArgIcit(i), ty))
        <|> bind.map(x => (List(x), ArgIcit(Expl), None))

    private lazy val lam: Parsley[Tm] =
      positioned(
        ("\\" *> many(lamParam) <~> "=>" *> tm).map(lamFromLamParams _)
      )

    private lazy val app: Parsley[Tm] =
      precedence[Tm](appAtom <|> lam)(
        defaultOps(
          (op, t) => App(Var(op), t, ArgIcit(Expl)),
          (op, l, r) => App(App(Var(op), l, ArgIcit(Expl)), r, ArgIcit(Expl))
        )*
      )

    private lazy val appAtom: Parsley[Tm] = positioned(
      (projAtom <~> many(arg) <~> option(lam <|> doP <|> matchP <|> ifP))
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

    // operators
    private def userOpStart(s: String): Parsley[String] =
      userOp0.filter(_.startsWith(s))

    private def opL[T](
        o: String,
        handle: (Name, T, T) => T
    ): Parsley[InfixL.Op[T]] =
      attempt(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
        (l, r) => handle(Name(op), l, r)
      )

    private def opR[T](
        o: String,
        handle: (Name, T, T) => T
    ): Parsley[InfixR.Op[T]] =
      attempt(userOpStart(o)).map(op => (l, r) => handle(Name(op), l, r))

    private def opP[T](
        o: String,
        handle: (Name, T) => T
    ): Parsley[Prefix.Op[T]] =
      attempt(userOpStart(o)).map(op => t => handle(Name(op), t))

    private def opLevel[T](
        s: String,
        prefix: (Name, T) => T,
        infix: (Name, T, T) => T
    ): List[Ops[T, T]] =
      val chars = s.toList
      List(
        Ops(Prefix)(chars.map(c => opP(c.toString, prefix))*),
        Ops(InfixL)(chars.map(c => opL(c.toString, infix))*),
        Ops(InfixR)(chars.map(c => opR(c.toString, infix))*)
      )

    private def ops[T](prefix: (Name, T) => T, infix: (Name, T, T) => T)(
        ss: String*
    ): List[Ops[T, T]] = ss.flatMap(s => opLevel(s, prefix, infix)).toList

    private def defaultOps[T](
        prefix: (Name, T) => T,
        infix: (Name, T, T) => T
    ): List[Ops[T, T]] =
      ops(prefix, infix)(
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
      )

    // definitions
    lazy val defs: Parsley[Defs] = many(defP <|> dataDefP).map(Defs.apply)

    private lazy val defP: Parsley[Def] =
      (pos <~> "def" *> option("rec") <~> identOrOp <~> many(
        defParam
      ) <~> option(
        ":" *> tm
      ) <~> (":=" #> false <|> "=" #> true) <~> tm)
        .map { case ((((((pos, rec), x), ps), ty), m), v) =>
          DDef(
            pos,
            x,
            rec.isDefined,
            m,
            ty.map(typeFromParams(m, ps, _)),
            lamFromDefParams(ps, v, ty.isEmpty)
          )
        }

    private lazy val datakindP: Parsley[SDataKind] =
      "(" *> (("boxed" #> SBoxed) <|> ("unboxed" #> SUnboxed) <|> ("newtype" #> SNewtype)) <* ")"

    private lazy val dataDefP: Parsley[Def] =
      (pos <~> "data" *> option(datakindP) <~> identOrOp <~> many(
        identOrOp
      ) <~> option(
        (":=" <|> "|") *> sepBy(
          pos <~> identOrOp <~> many(
            attempt("(" *> bind <~> ":" *> tm <* ")") <|> projAtom.map(t =>
              (DontBind, t)
            )
          ),
          "|"
        )
      ))
        .map { case ((((pos, k), x), ps), cs) =>
          DData(
            pos,
            k.getOrElse(SBoxed),
            x,
            ps,
            cs.map(cs => cs.map { case ((pos, x), ts) => DataCon(pos, x, ts) })
              .getOrElse(Nil)
          )
        }

  lazy val parser: Parsley[Tm] = LangLexer.fully(TmParser.tm)
  lazy val defsParser: Parsley[Defs] = LangLexer.fully(TmParser.defs)
