package core

import common.Common.*
import Syntax.*
import Value.*
import Metas.*
import Globals.*

import scala.annotation.tailrec

object Evaluation:
  // closures
  extension (c: Clos0)
    inline def apply(v: Val0): Val0 = c match
      case CClos0(env, tm) => eval0(tm)(E0(env, v))
      case CFun0(f)        => f(v)
  extension (c: Clos1)
    inline def apply(v: Val1): Val1 = c match
      case CClos1(env, tm) => eval1(tm)(E1(env, v))
      case CFun1(f)        => f(v)
    inline def apply(v: Val0): Val1 = c match
      case CClos1(env, tm) => eval1(tm)(E0(env, v))
      case CFun1(_)        => impossible()

  // evaluation
  @tailrec
  def vvar0(ix: Ix)(implicit e: Env): Val0 =
    e match
      case E0(_, v) if ix.expose == 0 => v
      case E0(env, _)                 => vvar0(ix - 1)(env)
      case E1(env, _)                 => vvar0(ix - 1)(env)
      case EEmpty                     => impossible()

  @tailrec
  def vvar1(ix: Ix)(implicit e: Env): Val1 =
    e match
      case E1(_, v) if ix.expose == 0 => v
      case E0(env, _)                 => vvar1(ix - 1)(env)
      case E1(env, _)                 => vvar1(ix - 1)(env)
      case EEmpty                     => impossible()

  def vglobal1(x: Name): Val1 =
    getGlobal(x) match
      case Some(GlobalEntry1(_, _, _, v, _)) =>
        VUnfold(UGlobal(x), SId, () => v)
      case _ => impossible()

  inline def vmeta(id: MetaId): Val1 = getMeta(id) match
    case Unsolved(_, _)   => VFlex(id, SId)
    case Solved(value, _) => VUnfold(UMeta(id), SId, () => value)

  inline def vpostponed(id: PostponedId)(implicit env: Env): Val1 =
    getPostponed(id) match
      case PECheck1(ctx, tm, ty, id)     => vappPruning(vmeta(id), ctx.pruning)
      case PECheckVarU1(ctx, tm, ty, id) => vappPruning(vmeta(id), ctx.pruning)
      case PECheck1Done(_, Some(tm))     => eval1(tm)
      case PECheck1Done(_, None)         => impossible()

  inline def vsplice(v: Val1): Val0 = v match
    case VQuote(v) => v
    case v         => VSplice(v)

  inline def vquote(v: Val0): Val1 = v match
    case VSplice(v) => v
    case v          => VQuote(v)

  def vapp1(f: Val1, a: Val1, i: Icit): Val1 = f match
    case VLam1(x, _, _, b) => b(a)
    case VFlex(id, sp)     => VFlex(id, SApp(sp, a, i))
    case VRigid(h, sp)     => VRigid(h, SApp(sp, a, i))
    case VUnfold(h, sp, v) => VUnfold(h, SApp(sp, a, i), () => vapp1(v(), a, i))
    case _                 => impossible()

  def vmetaapp(f: Val1, a: Either[Val0, Val1]): Val1 = (f, a) match
    case (VMetaLam(true, b), Right(a)) => b(a)
    case (VMetaLam(false, b), Left(a)) => b(a)
    case (VFlex(id, sp), a)            => VFlex(id, SMetaApp(sp, a))
    case (VUnfold(h, sp, v), a) =>
      VUnfold(h, SMetaApp(sp, a), () => vmetaapp(v(), a))
    case _ => impossible()

  def vprimelim(
      x: Name,
      scrut: Val1,
      ix: Int,
      i: Icit,
      as: List[(Val1, Icit)]
  ): Val1 = (x.expose, scrut) match
    case ("elimRep", VPrim1(Name("BoolRep")))   => as(1)._1
    case ("elimRep", VPrim1(Name("CharRep")))   => as(2)._1
    case ("elimRep", VPrim1(Name("ByteRep")))   => as(3)._1
    case ("elimRep", VPrim1(Name("ShortRep")))  => as(4)._1
    case ("elimRep", VPrim1(Name("IntRep")))    => as(5)._1
    case ("elimRep", VPrim1(Name("LongRep")))   => as(6)._1
    case ("elimRep", VPrim1(Name("FloatRep")))  => as(7)._1
    case ("elimRep", VPrim1(Name("DoubleRep"))) => as(8)._1

    case ("elimBoxity", VPrim1(Name("Boxed"))) => as(1)._1
    case ("elimBoxity", VRigid(HPrim(Name("Unboxed")), SApp(SId, rep, Expl))) =>
      vapp1(as(2)._1, rep, Expl)

    case (_, VFlex(id, sp)) => VFlex(id, SPrim(sp, ix, i, x, as))
    case (_, VRigid(h, sp)) => VRigid(h, SPrim(sp, ix, i, x, as))
    case (_, VUnfold(h, sp, v)) =>
      VUnfold(h, SPrim(sp, ix, i, x, as), () => vprimelim(x, v(), ix, i, as))
    case _ => impossible()

  def vspine(v: Val1, sp: Spine): Val1 = sp match
    case SId                     => v
    case SApp(sp, a, i)          => vapp1(vspine(v, sp), a, i)
    case SMetaApp(sp, a)         => vmetaapp(vspine(v, sp), a)
    case SPrim(sp, ix, i, x, as) => vprimelim(x, vspine(v, sp), ix, i, as)

  def vappPruning(v: Val1, p: Pruning)(implicit env: Env): Val1 =
    (env, p) match
      case (EEmpty, Nil)             => v
      case (E1(env, _), PESkip :: p) => vappPruning(v, p)(env)
      case (E0(env, _), PESkip :: p) => vappPruning(v, p)(env)
      case (E1(env, u), PEBind1(i) :: p) =>
        vmetaapp(vappPruning(v, p)(env), Right(u))
      case (E0(env, u), PEBind0 :: p) =>
        vmetaapp(vappPruning(v, p)(env), Left(u))
      case _ => impossible()

  def eval0(t: Tm0)(implicit env: Env): Val0 =
    t match
      case Var0(ix)     => vvar0(ix)
      case Global0(x)   => VGlobal0(x)
      case Prim0(x)     => VPrim0(x)
      case IntLit(v)    => VIntLit(v)
      case StringLit(v) => VStringLit(v)
      case Let0(x, ty, v, b) =>
        VLet0(x, eval1(ty), eval0(v), Clos0(b))
      case LetRec(x, ty, v, b) =>
        VLetRec(x, eval1(ty), Clos0(v), Clos0(b))
      case Lam0(x, ty, b)  => VLam0(x, eval1(ty), Clos0(b))
      case App0(f, a)      => VApp0(eval0(f), eval0(a))
      case Con(x, t, args) => VCon(x, eval1(t), args.map(eval0))
      case Match(scrut, t, c, ps, b, o) =>
        VMatch(eval0(scrut), eval1(t), c, ps.map(eval1), eval0(b), eval0(o))
      case Impossible(ty) => VImpossible(eval1(ty))
      case Splice(t)      => vsplice(eval1(t))
      case Foreign(io, ty, code, args) =>
        VForeign(io, eval1(ty), eval1(code), args.map(eval0))
      case Wk10(t) => eval0(t)(env.wk1)
      case Wk00(t) => eval0(t)(env.wk0)

  def eval1(t: Tm1)(implicit env: Env): Val1 =
    t match
      case Var1(ix)             => vvar1(ix)
      case Global1(x)           => vglobal1(x)
      case Prim1(x)             => vprim1(x)
      case Let1(_, _, v, b)     => eval1(b)(E1(env, eval1(v)))
      case U0(cv)               => VU0(eval1(cv))
      case U1                   => VU1
      case Pi(x, i, ty, b)      => VPi(x, i, eval1(ty), Clos1(b))
      case Lam1(x, i, ty, b)    => VLam1(x, i, eval1(ty), Clos1(b))
      case App1(f, a, i)        => vapp1(eval1(f), eval1(a), i)
      case TCon(x)              => VTCon(x)
      case Fun(l, p, cv, r)     => VFun(eval1(l), eval1(p), eval1(cv), eval1(r))
      case CV1                  => VCV1
      case Comp                 => VComp
      case LabelLit(v)          => VLabelLit(v)
      case Lift(cv, ty)         => VLift(eval1(cv), eval1(ty))
      case Quote(tm)            => vquote(eval0(tm))
      case AppPruning(m, p)     => vappPruning(vmeta(m), p)
      case Wk01(tm)             => eval1(tm)(env.wk0)
      case Wk11(tm)             => eval1(tm)(env.wk1)
      case Meta(id)             => vmeta(id)
      case MetaPi(m, t, b)      => VMetaPi(m, eval1(t), Clos1(b))
      case MetaLam(m, b)        => VMetaLam(m, Clos1(b))
      case MetaApp(f, Right(a)) => vmetaapp(eval1(f), Right(eval1(a)))
      case MetaApp(f, Left(a))  => vmetaapp(eval1(f), Left(eval0(a)))
      case PostponedCheck1(id)  => vpostponed(id)

  // forcing
  def force1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_, _) => top
        case Solved(v, _)   => VUnfold(UMeta(id), sp, () => vspine(v, sp))
    case v => v

  @tailrec
  def forceAll1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_, _) => top
        case Solved(v, _)   => forceAll1(vspine(v, sp))
    case VUnfold(_, _, v) => forceAll1(v())
    case v                => v

  @tailrec
  def forceAll0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceAll1(v) match
        case VQuote(v) => forceAll0(v)
        case _         => top
    case v => v

  @tailrec
  def forceMetas1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_, _) => top
        case Solved(v, _)   => forceMetas1(vspine(v, sp))
    case VUnfold(UMeta(_), _, v) => forceMetas1(v())
    case v                       => v

  @tailrec
  def forceMetas0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceMetas1(v) match
        case VQuote(v) => forceMetas0(v)
        case _         => top
    case v => v

  @tailrec
  def forceStage0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceAll1(v) match
        case VQuote(v) => forceStage0(v)
        case _         => top
    case v => v

  @tailrec
  def forceStage1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_, _) => top
        case Solved(v, _)   => forceStage1(vspine(v, sp))
    case VUnfold(_, _, v) => forceStage1(v())
    case v                => v

  // quoting
  enum QuoteOption:
    case UnfoldAll
    case UnfoldMetas
    case UnfoldNone
    case UnfoldStage
  export QuoteOption.*

  private def quote1(h: Tm1, sp: Spine, q: QuoteOption)(implicit
      lvl: Lvl
  ): Tm1 = sp match
    case SId            => h
    case SApp(sp, v, i) => App1(quote1(h, sp, q), quote1(v, q), i)
    case SMetaApp(sp, v) =>
      val a = v match
        case Left(v)  => Left(quote0(v, q))
        case Right(v) => Right(quote1(v, q))
      MetaApp(quote1(h, sp, q), a)
    case SPrim(sp, ix, i, x, as) =>
      val args =
        as.map((v, i) => (quote1(v, q), i))
          .patch(ix, List((quote1(h, sp, q), i)), 0)
      args.foldLeft(Prim1(x)) { case (f, (a, i)) => App1(f, a, i) }

  def quote1(v: Val1, q: QuoteOption)(implicit lvl: Lvl): Tm1 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goSp(h: Tm1, sp: Spine): Tm1 = quote1(h, sp, q)
    inline def goClos(c: Clos1): Tm1 = quote1(c(VVar1(lvl)), q)(lvl + 1)
    inline def goClos0(c: Clos1): Tm1 = quote1(c(VVar0(lvl)), q)(lvl + 1)
    inline def force(v: Val1): Val1 = q match
      case UnfoldAll   => forceAll1(v)
      case UnfoldMetas => forceMetas1(v)
      case UnfoldNone  => force1(v)
      case UnfoldStage => forceStage1(v)
    force(v) match
      case VRigid(hd, sp) =>
        hd match
          case HVar(lvl) => goSp(Var1(lvl.toIx), sp)
          case HPrim(x)  => goSp(Prim1(x), sp)
          case HTCon(x)  => goSp(TCon(x), sp)
      case VFlex(id, sp)              => goSp(Meta(id), sp)
      case VUnfold(UMeta(id), sp, _)  => goSp(Meta(id), sp)
      case VUnfold(UGlobal(x), sp, _) => goSp(Global1(x), sp)
      case VPi(x, i, ty, b)           => Pi(x, i, go1(ty), goClos(b))
      case VLam1(x, i, ty, b)         => Lam1(x, i, go1(ty), goClos(b))
      case VU0(cv)                    => U0(go1(cv))
      case VU1                        => U1
      case VFun(l, pty, cv, rty) => Fun(go1(l), go1(pty), go1(cv), go1(rty))
      case VCV1                  => CV1
      case VComp                 => Comp
      case VLabelLit(v)          => LabelLit(v)
      case VLift(cv, ty)         => Lift(go1(cv), go1(ty))
      case VQuote(tm)            => quote(go0(tm))
      case VMetaPi(m, t, b) =>
        MetaPi(m, go1(t), if m then goClos(b) else goClos0(b))
      case VMetaLam(m, b) => MetaLam(m, if m then goClos(b) else goClos0(b))

  def quote0(v: Val0, q: QuoteOption)(implicit lvl: Lvl): Tm0 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goClos(c: Clos0): Tm0 = quote0(c(VVar0(lvl)), q)(lvl + 1)
    inline def force(v: Val0): Val0 = q match
      case UnfoldAll   => forceAll0(v)
      case UnfoldMetas => forceMetas0(v)
      case UnfoldNone  => v
      case UnfoldStage => forceStage0(v)
    force(v) match
      case VVar0(x)      => Var0(x.toIx)
      case VGlobal0(x)   => Global0(x)
      case VPrim0(x)     => Prim0(x)
      case VIntLit(v)    => IntLit(v)
      case VStringLit(v) => StringLit(v)
      case VLet0(x, ty, v, b) =>
        Let0(x, go1(ty), go0(v), goClos(b))
      case VLetRec(x, ty, v, b) =>
        LetRec(x, go1(ty), goClos(v), goClos(b))
      case VLam0(x, ty, b)  => Lam0(x, go1(ty), goClos(b))
      case VApp0(f, a)      => App0(go0(f), go0(a))
      case VCon(x, t, args) => Con(x, go1(t), args.map(a => go0(a)))
      case VMatch(scrut, t, c, ps, b, o) =>
        Match(go0(scrut), go1(t), c, ps.map(p => go1(p)), go0(b), go0(o))
      case VImpossible(ty) => Impossible(go1(ty))
      case VSplice(tm)     => splice(go1(tm))
      case VForeign(io, ty, code, args) =>
        Foreign(io, go1(ty), go1(code), args.map(x => go0(x)))

  def nf(tm: Tm1, q: QuoteOption = UnfoldAll): Tm1 =
    quote1(eval1(tm)(EEmpty), q)(lvl0)
  def stage(tm: Tm0): Tm0 = quote0(eval0(tm)(EEmpty), UnfoldStage)(lvl0)
  def stageUnder(tm: Tm0, env: Env): Tm0 =
    quote0(eval0(tm)(env), UnfoldStage)(mkLvl(env.size))

  // primitives
  def vprim1(x: Name): Val1 = x.expose match
    case "elimRep" =>
      val rep = VPrim1(Name("Rep"))
      vlam1(
        "P",
        vfun1(rep, VU1),
        p =>
          vlam1(
            "rep",
            rep,
            rep =>
              vlam1(
                "BoolRep",
                vapp1(p, VPrim1(Name("BoolRep")), Expl),
                boolRep =>
                  vlam1(
                    "CharRep",
                    vapp1(p, VPrim1(Name("CharRep")), Expl),
                    charRep =>
                      vlam1(
                        "ByteRep",
                        vapp1(p, VPrim1(Name("ByteRep")), Expl),
                        byteRep =>
                          vlam1(
                            "ShortRep",
                            vapp1(p, VPrim1(Name("ShortRep")), Expl),
                            shortRep =>
                              vlam1(
                                "IntRep",
                                vapp1(
                                  p,
                                  VPrim1(Name("IntRep")),
                                  Expl
                                ),
                                intRep =>
                                  vlam1(
                                    "LongRep",
                                    vapp1(
                                      p,
                                      VPrim1(Name("LongRep")),
                                      Expl
                                    ),
                                    longRep =>
                                      vlam1(
                                        "FloatRep",
                                        vapp1(
                                          p,
                                          VPrim1(Name("FloatRep")),
                                          Expl
                                        ),
                                        floatRep =>
                                          vlam1(
                                            "DoubleRep",
                                            vapp1(
                                              p,
                                              VPrim1(Name("DoubleRep")),
                                              Expl
                                            ),
                                            doubleRep =>
                                              vprimelim(
                                                x,
                                                rep,
                                                1,
                                                Expl,
                                                List(
                                                  (p, Expl),
                                                  (boolRep, Expl),
                                                  (charRep, Expl),
                                                  (byteRep, Expl),
                                                  (shortRep, Expl),
                                                  (intRep, Expl),
                                                  (longRep, Expl),
                                                  (floatRep, Expl),
                                                  (longRep, Expl)
                                                )
                                              )
                                          )
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
          )
      )
    case "elimBoxity" =>
      val boxity = VPrim1(Name("Boxity"))
      vlam1(
        "P",
        boxity,
        p =>
          vlam1(
            "boxity",
            boxity,
            b =>
              vlam1(
                "Boxed",
                vapp1(p, VPrim1(Name("Boxed")), Expl),
                boxed =>
                  vlam1(
                    "Unboxed",
                    vlam1(
                      "rep",
                      VPrim1(Name("Rep")),
                      rep =>
                        vapp1(
                          p,
                          vapp1(VPrim1(Name("Unboxed")), rep, Expl),
                          Expl
                        )
                    ),
                    unboxed =>
                      vprimelim(
                        x,
                        b,
                        1,
                        Expl,
                        List((p, Expl), (boxed, Expl), (unboxed, Expl))
                      )
                  )
              )
          )
      )
    case _ => VPrim1(x)
