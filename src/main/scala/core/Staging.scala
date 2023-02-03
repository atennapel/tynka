package core

import common.Common.*
import common.Debug.debug
import Syntax.*
import Globals.getGlobal
import ir.Syntax as IR

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer

object Staging:
  // evaluation
  private enum Env:
    case Empty
    case Def0(e: Env, v: Val0)
    case Def1(e: Env, v: Val1)

    def tail: Env = this match
      case Def0(e, _) => e
      case Def1(e, _) => e
      case _          => impossible()
  import Env.*

  private enum Val1:
    case VPrim1(x: PrimName, args: List[Val1])
    case VLam1(fn: Val1 => Val1)
    case VQuote1(v: Val0)
    case VType1
    case VTPair1(fst: Val1, snd: Val1)
    case VPair1(fst: Val1, snd: Val1)
    case VTCon1(cs: Val1 => List[List[Val1]])
    case VTConName1(x: IR.GName)
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(x: Name, ty: Val1)
    case VPrim0(x: PrimName)
    case VSplicePrim0(x: PrimName, as: List[Val1])
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VFix0(ty: Val1, rty: Val1, b: (Val0, Val0) => Val0, arg: Val0)
    case VLet0(ty: Val1, bty: Val1, value: Val0, body: Val0 => Val0)
    case VIntLit0(n: Int)
    case VCon0(ty: Val1, ix: Int, as: List[Val0])
    case VCase0(ty: Val1, rty: Val1, scrut: Val0, cs: List[Val0])
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(e: Env, i: Int): Val1 = (e, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), x) => go(e, x - 1)
      case (Def0(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = (f, a) match
    case (VLam1(f), _)               => f(a)
    case (VPrim1(x, as), _)          => VPrim1(x, as ++ List(a))
    case (VQuote1(f), VQuote1(a))    => VQuote1(VApp0(f, a))
    case (VQuote1(f), VPrim1(p, as)) => VQuote1(VApp0(f, VSplicePrim0(p, as)))
    case _                           => impossible()

  private def vproj1(t: Val1, p: ProjType): Val1 = (t, p) match
    case (VPair1(fst, _), Fst)         => fst
    case (VPair1(_, snd), Snd)         => snd
    case (VPair1(fst, _), Named(_, 0)) => fst
    case (VPair1(_, snd), Named(x, i)) => vproj1(snd, Named(x, i - 1))
    case _                             => impossible()

  private def clos1(t: Tm)(implicit env: Env): Val1 => Val1 =
    v => eval1(t)(Def1(env, v))

  private def eval1(t: Tm)(implicit env: Env): Val1 = t match
    case Var(x)                => vvar1(x)
    case Global(x)             => eval1(getGlobal(x).get.tm)
    case Prim(x)               => VPrim1(x, Nil)
    case Lam(_, _, _, b)       => VLam1(clos1(b))
    case App(f, a, _)          => vapp1(eval1(f), eval1(a))
    case Proj(t, p, _, _)      => vproj1(eval1(t), p)
    case Let(_, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case TPair(fst, snd)       => VTPair1(eval1(fst), eval1(snd))
    case Pair(fst, snd, _)     => VPair1(eval1(fst), eval1(snd))
    case TCon(_, cs) =>
      VTCon1(r => cs.map(as => as.map(a => eval1(a)(Def1(env, r)))))
    case Quote(t) => VQuote1(eval0(t))
    case Wk(t)    => eval1(t)(env.tail)

    case U(_)           => VType1
    case Pi(_, _, _, _) => VType1
    case Sigma(_, _, _) => VType1
    case Lift(_, _)     => VType1
    case Irrelevant     => VType1

    case _ => impossible()

  private def vvar0(ix: Ix)(implicit env: Env): Val0 =
    def go(e: Env, i: Int): Val0 = (e, i) match
      case (Def0(_, v), 0) => v
      case (Def0(e, _), x) => go(e, x - 1)
      case (Def1(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vsplice0(v: Val1): Val0 = v match
    case VQuote1(v)    => v
    case VPrim1(x, as) => VSplicePrim0(x, as)
    case _             => impossible()

  private def vpairTy1Clos(a: Val1, b: Val1): Val1 => List[List[Val1]] = _ =>
    List(List(a, b))
  private def vpairTy1(a: Val1, b: Val1): Val1 = VTCon1(vpairTy1Clos(a, b))

  private def vproj0(v: Val0, p: ProjType, t: Val1, pt: Val1): Val0 =
    val VTPair1(a, b) = pt: @unchecked
    (v, p) match
      case (p, Fst) =>
        VCase0(
          vpairTy1(a, b),
          a,
          v,
          List(
            VLam0(
              VPrim1(
                PTFun,
                List(
                  a,
                  VPrim1(PFun, Nil),
                  VPrim1(PTFun, List(b, VPrim1(PVal, Nil), a))
                )
              ),
              fst =>
                VLam0(VPrim1(PTFun, List(b, VPrim1(PVal, Nil), a)), snd => fst)
            )
          )
        )
      case (p, Snd) =>
        VCase0(
          vpairTy1(a, b),
          b,
          v,
          List(
            VLam0(
              VPrim1(
                PTFun,
                List(
                  a,
                  VPrim1(PFun, Nil),
                  VPrim1(PTFun, List(b, VPrim1(PVal, Nil), b))
                )
              ),
              fst =>
                VLam0(VPrim1(PTFun, List(b, VPrim1(PVal, Nil), b)), snd => snd)
            )
          )
        )
      case _ => impossible()

  private def clos0(t: Tm)(implicit env: Env): Val0 => Val0 =
    v => eval0(t)(Def0(env, v))

  private def eval0(t: Tm)(implicit env: Env): Val0 = t match
    case Var(x)             => vvar0(x)
    case Global(x)          => VGlobal0(x, eval1(getGlobal(x).get.ty)(Empty))
    case Prim(x)            => VPrim0(x)
    case Lam(x, _, fnty, b) => VLam0(eval1(fnty), clos0(b))
    case Fix(ty, rty, g, x, b, arg) =>
      VFix0(
        eval1(ty),
        eval1(rty),
        (v, w) => eval0(b)(Def0(Def0(env, v), w)),
        eval0(arg)
      )
    case App(f, a, _)        => VApp0(eval0(f), eval0(a))
    case Proj(t, p, ty, pty) => vproj0(eval0(t), p, eval1(ty), eval1(pty))
    case Let(x, t, _, bt, v, b) =>
      VLet0(eval1(t), eval1(bt), eval0(v), clos0(b))
    case Pair(fst, snd, ty) =>
      val VTPair1(a, b) = eval1(ty): @unchecked
      VCon0(vpairTy1(a, b), 0, List(eval0(fst), eval0(snd)))
    case Splice(t)      => vsplice0(eval1(t))
    case Wk(t)          => eval0(t)(env.tail)
    case IntLit(n)      => VIntLit0(n)
    case Con(ty, i, as) => VCon0(eval1(ty), i, as.map(eval0))
    case Case(ty, rty, s, cs) =>
      VCase0(eval1(ty), eval1(rty), eval0(s), cs.map(eval0))
    case _ => impossible()

  // intermediate rep
  private type RDs = List[RD]

  private enum RD:
    case Def(name: IR.GName, gen: Boolean, ty: IR.TDef, value: R)

    override def toString: String = this match
      case Def(x, _, t, v) => s"def $x : $t = $v"

  private type RCase = (List[(IR.LName, IR.Ty)], R)
  private enum R:
    case Var(name: IR.LName, ty: IR.TDef)
    case Global(name: IR.GName, ty: IR.TDef)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case App(fn: R, arg: R)
    case PrimApp(name: PrimName, args: List[R])
    case Lam(name: IR.LName, t1: IR.Ty, t2: IR.TDef, body: R)
    case Let(name: IR.LName, ty: IR.TDef, bty: IR.TDef, value: R, body: R)

    case Con(ty: IR.GName, ix: Int, as: List[R])
    case Case(ty: IR.GName, rty: IR.TDef, scrut: R, cs: List[RCase])

    case Fix(t1: IR.Ty, t2: IR.TDef, go: IR.LName, x: IR.LName, body: R, arg: R)

    case Box(t: IR.Ty, v: R)
    case Unbox(t: IR.Ty, v: R)

    override def toString: String = this match
      case Var(x, _)    => s"'$x"
      case Global(x, _) => s"$x"

      case IntLit(v)  => s"$v"
      case BoolLit(b) => if b then "True" else "False"

      case App(f, a)          => s"($f $a)"
      case PrimApp(p, Nil)    => s"$p"
      case PrimApp(p, as)     => s"($p ${as.mkString(" ")})"
      case Lam(x, t, _, b)    => s"(\\($x : $t). $b)"
      case Let(x, t, _, v, b) => s"(let $x : $t = $v; $b)"

      case Con(ty, i, Nil)     => s"(con $ty #$i)"
      case Con(ty, i, as)      => s"(con $ty #$i ${as.mkString(" ")})"
      case Case(ty, _, s, Nil) => s"(case $ty $s)"
      case Case(ty, _, s, cs) =>
        def csStr(c: RCase) = c match
          case (Nil, b) => b.toString
          case (xs, b) =>
            s"(${xs.map((x, t) => s"($x : $t)").mkString(" ")}. $b)"
        s"(case $ty $s ${cs.map(csStr).mkString(" ")})"

      case Fix(t1, t2, go, x, b, arg) =>
        s"(fix (($go : ${IR.TDef(t1, t2)}) ($x : $t1). $b) $arg)"

      case Box(_, v)   => s"(box $v)"
      case Unbox(_, v) => s"(unbox $v)"

    def lams(ps: List[(IR.LName, IR.Ty)], rt: IR.TDef): R =
      ps.foldRight[(R, IR.TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (R.Lam(x, t, rt, b), IR.TDef(t :: rt.ps, rt.rt))
      }._1

    def flattenLams: (List[(IR.LName, IR.Ty)], Option[IR.Ty], R) =
      def go(t: R): (List[(IR.LName, IR.Ty)], Option[IR.Ty], R) = t match
        case Lam(x, t1, t2, b) =>
          val (xs, rt, b2) = go(b)
          ((x, t1) :: xs, rt.fold(Some(t2.rt))(t => Some(t)), b2)
        case b => (Nil, None, b)
      go(this)

    def apps(args: List[R]) = args.foldLeft(this)(App.apply)

    def flattenApps: (R, List[R]) = this match
      case App(f, a) =>
        val (hd, as) = f.flattenApps
        (hd, as ++ List(a))
      case t => (t, Nil)

    def fvs: List[(IR.LName, IR.TDef)] = this match
      case Var(x, t)    => List((x, t))
      case Global(x, _) => Nil

      case IntLit(n)  => Nil
      case BoolLit(n) => Nil

      case App(f, a)          => f.fvs ++ a.fvs
      case PrimApp(p, as)     => as.flatMap(_.fvs)
      case Lam(x, _, _, b)    => b.fvs.filterNot((y, _) => y == x)
      case Let(x, _, _, v, b) => v.fvs ++ b.fvs.filterNot((y, _) => x == y)

      case Con(_, _, as) => as.flatMap(_.fvs)
      case Case(_, _, s, cs) =>
        s.fvs ++ cs.flatMap((xs, b) =>
          b.fvs.filterNot((y, _) => xs.exists((z, _) => z == y))
        )

      case Fix(_, _, go, x, b, arg) =>
        b.fvs.filterNot((y, _) => y == go || y == x) ++ arg.fvs

      case Box(_, v)   => v.fvs
      case Unbox(_, v) => v.fvs

    def subst(sub: Map[IR.LName, R]): R =
      subst(
        sub,
        sub.values
          .foldRight(Set.empty[IR.LName])((a, b) => a.fvs.map(_._1).toSet ++ b)
      )
    def subst(sub: Map[IR.LName, R], scope: Set[IR.LName]): R =
      def underN(
          ps: List[(IR.LName, IR.TDef)],
          b: R,
          sub: Map[IR.LName, R],
          scope: Set[IR.LName]
      ): (List[(IR.LName, IR.TDef)], R) =
        def go(
            ps: List[(IR.LName, IR.TDef)],
            nps: List[(IR.LName, IR.TDef)],
            sub: Map[IR.LName, R],
            scope: Set[IR.LName]
        ): (List[(IR.LName, IR.TDef)], R) = ps match
          case Nil => (nps, b.subst(sub, scope))
          case (x, t) :: ps =>
            if scope.contains(x) then
              val y = scope.max
              go(
                ps,
                nps ++ List((y, t)),
                sub + (x -> Var(y, t)),
                scope + y
              )
            else go(ps, nps ++ List((x, t)), sub - x, scope + x)
        go(ps, Nil, sub, scope)
      this match
        case Var(x, _)    => sub.get(x).getOrElse(this)
        case Global(x, _) => this

        case IntLit(n)  => this
        case BoolLit(n) => this

        case App(f, a)      => App(f.subst(sub, scope), a.subst(sub, scope))
        case PrimApp(p, as) => PrimApp(p, as.map(_.subst(sub, scope)))
        case Lam(x0, t1, t2, b0) =>
          val (List((x, _)), b) =
            underN(List((x0, IR.TDef(t1))), b0, sub, scope)
          Lam(x, t1, t2, b)
        case Let(x0, t, bt, v, b0) =>
          val (List((x, _)), b) = underN(List((x0, t)), b0, sub, scope)
          Let(x, t, bt, v.subst(sub, scope), b)

        case Con(ty, i, as) => Con(ty, i, as.map(_.subst(sub, scope)))
        case Case(ty, rty, s, cs) =>
          Case(
            ty,
            rty,
            s.subst(sub, scope),
            cs.map((xs, b0) => {
              val (ps, b) =
                underN(xs.map((x, t) => (x, IR.TDef(t))), b0, sub, scope)
              (ps.map((x, t) => (x, t.ty)), b)
            })
          )

        case Fix(t1, t2, g0, x0, b0, arg) =>
          val (List((g, _), (x, _)), b) = underN(
            List((g0, IR.TDef(t1, t2)), (x0, IR.TDef(t1))),
            b0,
            sub,
            scope
          )
          Fix(t1, t2, g, x, b, arg.subst(sub, scope))

        case Box(t, v)   => Box(t, v.subst(sub, scope))
        case Unbox(t, v) => Unbox(t, v.subst(sub, scope))

  // quotation
  private type DataMap =
    ArrayBuffer[(Val1 => List[List[Val1]], List[List[IR.Ty]])]

  private def tyMatch(a: Val1, b: Val1)(implicit l: Int): Boolean = (a, b) match
    case (VPrim1(PTBox, List(_)), VPrim1(PTBox, List(_))) => true
    case (VPrim1(x1, as1), VPrim1(x2, as2))
        if x1 == x2 && as1.size == as2.size =>
      as1.zip(as2).forall(tyMatch)
    case (VTCon1(cs1), VTCon1(cs2))     => dataMatch(cs1, cs2)
    case (VTConName1(x), VTConName1(y)) => x == y
    case _                              => false
  private def dataMatch(
      a: Val1 => List[List[Val1]],
      b: Val1 => List[List[Val1]]
  )(implicit l: Int): Boolean =
    val cs1 = a(VTConName1(s"X$l"))
    val cs2 = b(VTConName1(s"X$l"))
    cs1.size == cs2.size && cs1
      .zip(cs2)
      .forall((as1, as2) =>
        as1.size == as2.size && as1.zip(as2).forall(tyMatch)
      )

  private def findData(cs: Val1 => List[List[Val1]])(implicit
      dm: DataMap
  ): Int =
    dm.indexWhere((cs2, _) => dataMatch(cs, cs2)(0))

  private def addData(
      cs: Val1 => List[List[Val1]],
      k: (i: Int) => List[List[IR.Ty]]
  )(implicit
      dm: DataMap
  ): Int =
    val ix = findData(cs)
    if ix >= 0 then ix
    else
      val i = dm.size
      dm += ((cs, k(dm.size)))
      i

  private def findOrAddData(cs: Val1 => List[List[Val1]])(implicit
      dm: DataMap
  ): (Int, IR.GName) =
    val i = addData(
      cs,
      i => {
        val x = s"D$i"
        cs(VTConName1(x)).map(as => as.map(quoteVTy))
      }
    )
    (i, s"D$i")

  private def quoteVTy(v: Val1)(implicit dm: DataMap): IR.Ty = v match
    case VPrim1(PInt, Nil)      => IR.TInt
    case VTPair1(a, b)          => IR.TCon(findOrAddData(vpairTy1Clos(a, b))._2)
    case VTConName1(x)          => IR.TCon(x)
    case VTCon1(cs)             => IR.TCon(findOrAddData(cs)._2)
    case VPrim1(PTBox, List(_)) => IR.TBox
    case _                      => impossible()

  private def quoteFTy(v: Val1)(implicit dm: DataMap): IR.TDef = v match
    case VPrim1(PTFun, List(a, _, b)) => IR.TDef(quoteVTy(a), quoteFTy(b))
    case _                            => IR.TDef(quoteVTy(v))

  private type NS = List[(IR.LName, IR.TDef)]
  private type Fresh = () => IR.LName
  private type Emit = () => (IR.GName, RD => Unit)

  private def primOverApp(p: PrimName, n: Int, as: List[Val1])(implicit
      l: Lvl,
      ns: NS,
      fresh: Fresh,
      dm: DataMap
  ): R =
    val hd = quoteRep(VSplicePrim0(p, as.take(n)))
    val qas = as.drop(n).map(a => quoteRep(vsplice0(a)))
    qas.foldLeft(hd)((f, a) => R.App(f, a))
  private def quoteRep(
      v: Val0
  )(implicit l: Lvl, ns: NS, fresh: Fresh, dm: DataMap): R =
    v match
      case VVar0(lvl) =>
        val (x, t) = ns(lvl.toIx.expose)
        R.Var(x, t)
      case VGlobal0(x, t) => R.Global(x.expose, quoteFTy(t))

      case VIntLit0(v) => R.IntLit(v)

      case VApp0(f, a) =>
        def flatten(v: Val0): (Val0, List[Val0]) = v match
          case VApp0(f, a) =>
            val (hd, as) = flatten(f)
            (hd, as ++ List(a))
          case v => (v, Nil)
        val (hd, as) = flatten(v)
        hd match
          case VPrim0(p) => R.PrimApp(p, as.map(quoteRep))
          case _ =>
            val qhd = quoteRep(hd)
            as.map(quoteRep).foldLeft(qhd)(R.App.apply)
      case VLam0(ft, b) =>
        val x = fresh()
        val qt = quoteFTy(ft)
        R.Lam(
          x,
          qt.head,
          qt.tail,
          quoteRep(b(VVar0(l)))(l + 1, (x, IR.TDef(qt.head)) :: ns, fresh, dm)
        )
      case VLet0(ty, bt, v, b) =>
        val x = fresh()
        val qt = quoteFTy(ty)
        R.Let(
          x,
          qt,
          quoteFTy(bt),
          quoteRep(v),
          quoteRep(b(VVar0(l)))(l + 1, (x, qt) :: ns, fresh, dm)
        )

      case VCon0(VTCon1(cs), i, as) =>
        R.Con(findOrAddData(cs)._2, i, as.map(quoteRep))
      case VCase0(VTCon1(tcs), rty, scrut, cs) =>
        val (ix, dty) = findOrAddData(tcs)
        val ecs = dm(ix)._2
          .zip(cs)
          .map((ts, v) => {
            val xs = ts.map(t => (fresh(), t))
            val ev = xs.foldLeft(quoteRep(v)) { case (f, (x, t)) =>
              R.App(f, R.Var(x, IR.TDef(t)))
            }
            (xs, ev)
          })
        R.Case(dty, quoteFTy(rty), quoteRep(scrut), ecs)

      case VFix0(ty, rty, b, arg) =>
        val ta = quoteVTy(ty)
        val tb = quoteFTy(rty)
        val g = fresh()
        val x = fresh()
        val qf = quoteRep(b(VVar0(l), VVar0(l + 1)))(
          l + 2,
          (x, IR.TDef(ta)) :: (g, IR.TDef(ta, tb)) :: ns,
          fresh,
          dm
        )
        val qarg = quoteRep(arg)
        R.Fix(ta, tb, g, x, qf, qarg)

      case VSplicePrim0(PBox, List(t, v)) =>
        R.Box(quoteVTy(t), quoteRep(vsplice0(v)))
      case VSplicePrim0(PUnbox, List(t, v)) =>
        R.Unbox(quoteVTy(t), quoteRep(vsplice0(v)))

      case _ => impossible()

  private def eta(ps: List[IR.Ty])(implicit
      fresh: Fresh
  ): (List[(IR.LName, IR.Ty)], List[R]) =
    val vs =
      ps.foldLeft[List[(IR.LName, IR.Ty)]](Nil) { case (vs, ty) =>
        val x = fresh()
        vs ++ List((x, ty))
      }
    val spine = vs.map((x, t) => R.Var(x, IR.TDef(t)))
    (vs, spine)
  private def lambdaLift(tm: R)(implicit fresh: Fresh, emit: Emit): R =
    def isSmall(v: R): Boolean = v match
      case R.Var(_, _)      => true
      case R.Global(_, _)   => true
      case R.IntLit(_)      => true
      case R.Con(_, _, Nil) => true
      case _                => false
    def go(tm: R): R = tm match
      case R.App(f, a) =>
        go(f) match
          // (let x : t = v; b) a ~> let x : t = v; b a
          case R.Let(x, t, bt, v, b) =>
            go(R.Let(x, t, bt.tail, v, R.App(b, a)))
          // (\(x : t). b) a ~> let x : t = a; b
          case R.Lam(x, t1, t2, b) => go(R.Let(x, IR.TDef(t1), t2, a, b))
          case f                   => R.App(f, go(a))

      case R.PrimApp(p, as) =>
        (p, as.map(go)) match
          case (PIntAdd, List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a + b)
          case (PIntAdd, List(a, R.IntLit(0)))           => go(a)
          case (PIntAdd, List(R.IntLit(0), b))           => go(b)

          case (PIntSub, List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a - b)
          case (PIntSub, List(a, R.IntLit(0)))           => go(a)

          case (PIntMul, List(_, R.IntLit(0)))           => R.IntLit(0)
          case (PIntMul, List(R.IntLit(0), _))           => R.IntLit(0)
          case (PIntMul, List(a, R.IntLit(1)))           => go(a)
          case (PIntMul, List(R.IntLit(1), a))           => go(a)
          case (PIntMul, List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a * b)

          case (PIntDiv, List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a / b)
          case (PIntDiv, List(a, R.IntLit(1)))           => go(a)

          case (PIntMod, List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a % b)
          case (PIntMod, List(a, R.IntLit(1)))           => R.IntLit(0)

          case (PIntEq, List(R.IntLit(a), R.IntLit(b)))  => R.BoolLit(a == b)
          case (PIntNeq, List(R.IntLit(a), R.IntLit(b))) => R.BoolLit(a != b)
          case (PIntLt, List(R.IntLit(a), R.IntLit(b)))  => R.BoolLit(a < b)
          case (PIntGt, List(R.IntLit(a), R.IntLit(b)))  => R.BoolLit(a > b)
          case (PIntLeq, List(R.IntLit(a), R.IntLit(b))) => R.BoolLit(a <= b)
          case (PIntGeq, List(R.IntLit(a), R.IntLit(b))) => R.BoolLit(a >= b)

          case (p, as) => R.PrimApp(p, as)

      case R.Lam(x, t1, t2, b) => R.Lam(x, t1, t2, go(b))

      // let y : t2 = (let x : t1 = v; b1); b2 ~> let x : t1 = v; let y : t2 = b1; b2
      case R.Let(y, t2, bt2, R.Let(x, t1, bt1, v, b1), b2) =>
        go(R.Let(x, t1, bt2, v, R.Let(y, t2, bt2, b1, b2)))
      case R.Let(x, t, bt, v0, b) =>
        val v = go(v0)
        val c = b.fvs.count((y, _) => x == y)
        if c == 0 then go(b)
        else if c == 1 || isSmall(v) then go(b.subst(Map(x -> v)))
        else if t.ps.isEmpty then
          val (vs2, spine2) = eta(bt.ps)
          R.Let(
            x,
            t,
            bt,
            go(v),
            go(b.apps(spine2))
          ).lams(vs2, IR.TDef(bt.rt))
        else
          val (vs, spine) = eta(t.ps)
          val fv = v.fvs
            .map((x, t) => (x, t.ty))
            .distinctBy((y, _) => y)
          val nps = fv ++ vs
          val args = nps.zipWithIndex.map { case ((x, _), ix) =>
            x -> ix
          }.toMap
          val (gx, addDef) = emit()
          addDef(
            RD.Def(
              gx,
              true,
              IR.TDef(fv.map(_._2), t),
              go(v.apps(spine).lams(nps, IR.TDef(t.rt)))
            )
          )
          val gl = R
            .Global(gx, IR.TDef(nps.map(_._2), t.rt))
            .apps(fv.map((x, t) => R.Var(x, IR.TDef(t))))
          val (vs2, spine2) = eta(bt.ps)
          go(b.subst(Map(x -> gl)).apps(spine2).lams(vs2, IR.TDef(bt.rt)))

      case R.Con(ty, i, as) => R.Con(ty, i, as.map(go))
      case R.Case(ty, rty, scrut, cs) =>
        go(scrut) match
          case R.Con(_, i, as) =>
            val (xs, b) = cs(i)
            go(xs.zip(as).foldRight(b) { case (((x, t), v), b) =>
              R.Let(x, IR.TDef(t), rty, v, b)
            })
          case gscrut =>
            val (vs, spine) = eta(rty.ps)
            R.Case(
              ty,
              IR.TDef(rty.rt),
              gscrut,
              cs.map((xs, b) => (xs, go(b.apps(spine))))
            ).lams(vs, IR.TDef(rty.rt))

      case R.Fix(t1, t2, g, x, b0, arg) =>
        val (vs, spine) = eta(t2.ps)
        val fv = b0.fvs
          .filterNot((y, _) => y == g || y == x)
          .map((x, t) => (x, t.ty))
          .distinctBy((y, _) => y)
        val nps = fv ++ List((x, t1)) ++ vs
        val args = nps.zipWithIndex.map { case ((x, _), ix) =>
          x -> ix
        }.toMap
        val (gx, addDef) = emit()
        val gl = R
          .Global(gx, IR.TDef(nps.map(_._2), t2.rt))
          .apps(fv.map((x, t) => R.Var(x, IR.TDef(t))))
        val b = go(b0.apps(spine).lams(nps, IR.TDef(t2.rt)).subst(Map(g -> gl)))
        addDef(RD.Def(gx, true, IR.TDef(fv.map(_._2) ++ List(t1), t2), b))
        R.App(gl, go(arg))

      case R.Box(t, v) =>
        go(v) match
          case R.Unbox(t, v) => v
          case v             => R.Box(t, v)
      case R.Unbox(t, v) =>
        go(v) match
          case R.Box(t, v) => v
          case v           => R.Unbox(t, v)

      case tm => tm
    go(tm)

  // to IR
  private type IRNS = Map[IR.LName, IR.LName]
  private type Lets = List[(IR.LName, IR.Ty, IR.Comp)]

  private def c2v(
      tm: R
  )(implicit
      ns: IRNS,
      defname: IR.GName,
      fresh: Fresh
  ): (IR.Value, IR.Ty, Lets) =
    val (c, t, ds) = toIRComp(tm, false)
    c match
      case IR.Val(qv) => (qv, t, ds)
      case _ =>
        val x = fresh()
        (IR.Var(x), t, ds ++ List((x, t, c)))

  private def toIRValue(
      tm: R
  )(implicit
      ns: IRNS,
      defname: IR.GName,
      fresh: Fresh
  ): (IR.Value, IR.Ty, Lets) =
    tm match
      case R.Var(x, t) =>
        val ty = t.ty
        val y = ns(x)
        (IR.Var(y), ty, Nil)
      case R.Global(x, t) =>
        val ty = t.ty
        (IR.Global(x, ty), ty, Nil)

      case R.IntLit(v) => (IR.IntLit(v), IR.TInt, Nil)

      case R.Con(ty, i, as) =>
        val (qas, ds) = as.foldLeft[(List[IR.Value], Lets)]((Nil, Nil)) {
          case ((as, ds), a) =>
            val (qa, ta, nds) = toIRValue(a)
            (as ++ List(qa), ds ++ nds)
        }
        (IR.Con(ty, i, qas), IR.TCon(ty), ds)

      case R.Box(ty, v) =>
        val (qv, tv, ds) = toIRValue(v)
        (IR.Box(ty, qv), IR.TBox, ds)

      case _ => c2v(tm)

  private def v2c(
      tm: R
  )(implicit
      ns: IRNS,
      defname: IR.GName,
      fresh: Fresh
  ): (IR.Comp, IR.Ty, Lets) =
    val (v, t, ds) = toIRValue(tm)
    (IR.Val(v), t, ds)

  private def toIRComp(
      tm: R,
      tail: Boolean
  )(implicit
      ns: IRNS,
      defname: IR.GName,
      fresh: Fresh
  ): (IR.Comp, IR.Ty, Lets) = tm match
    case R.Var(_, _)    => v2c(tm)
    case R.Global(_, _) => v2c(tm)
    case R.IntLit(_)    => v2c(tm)
    case R.Con(_, _, _) => v2c(tm)
    case R.Box(_, _)    => v2c(tm)

    case R.App(_, _) =>
      val (f, as) = tm.flattenApps
      f match
        case R.Global(x, t) =>
          val (qas, ds) = as.foldLeft[(List[IR.Value], Lets)]((Nil, Nil)) {
            case ((as, ds), a) =>
              val (qa, ta, nds) = toIRValue(a)
              (as ++ List(qa), ds ++ nds)
          }
          (IR.GlobalApp(x, t, tail && x == defname, qas), t.rt, ds)
        case _ => impossible()
    case R.PrimApp(p, as) =>
      val rt = p match
        case PIntAdd => IR.TInt
        case PIntSub => IR.TInt
        case PIntMul => IR.TInt
        case PIntDiv => IR.TInt
        case PIntMod => IR.TInt

        case PIntEq  => IR.TBool
        case PIntNeq => IR.TBool
        case PIntLt  => IR.TBool
        case PIntGt  => IR.TBool
        case PIntLeq => IR.TBool
        case PIntGeq => IR.TBool
        case _       => impossible()
      val (qas, ds) = as.foldLeft[(List[IR.Value], Lets)]((Nil, Nil)) {
        case ((as, ds), a) =>
          val (qa, ta, nds) = toIRValue(a)
          (as ++ List(qa), ds ++ nds)
      }
      (IR.PrimApp(p, qas), rt, ds)

    case R.Let(x, t, bt, v, b) =>
      val (qv, tv, ds1) = toIRComp(v, false)
      val y = fresh()
      val (qb, tb, ds2) = toIRComp(b, tail)(ns + (x -> y), defname, fresh)
      (qb, tb, ds1 ++ List((y, tv, qv)) ++ ds2)

    case R.Case(ty, rty, s, cs) =>
      val (qs, ts, ds) = toIRValue(s)
      val qcs = cs.map((xs, b) =>
        val (newns, ys) = xs
          .foldLeft[(IRNS, List[(IR.LName, IR.Ty)])](
            (ns, Nil)
          ) { case ((newns, ys), (x, t)) =>
            val y = fresh()
            (newns + (x -> y), ys ++ List((y, t)))
          }
        (ys, toIRLet(b, tail)(newns, defname, fresh))
      )
      (IR.Case(ty, qs, qcs), rty.ty, ds)

    case R.Unbox(ty, v) =>
      val (qv, tv, ds) = toIRValue(v)
      (IR.Unbox(ty, qv), ty, ds)

    case _ => impossible()

  private def toIRLet(tm: R, tail: Boolean)(implicit
      ns: IRNS,
      defname: IR.GName,
      fresh: Fresh
  ): IR.Let =
    val (b, _, ds) = toIRComp(tm, tail)
    IR.Let(ds, b)

  private def toIRDef(d: RD)(implicit fresh: Fresh): IR.Def = d match
    case RD.Def(x, gen, t, v0) =>
      val (ps, _, v) = v0.flattenLams
      implicit val irns: IRNS = ps.map((x, _) => (x, fresh())).toMap
      implicit val defname: IR.GName = x
      IR.DDef(x, gen, t, ps.map((x, t) => (irns(x), t)), toIRLet(v, true))

  // staging
  private def stageFTy(t: Ty)(implicit dm: DataMap): IR.TDef =
    quoteFTy(eval1(t)(Empty))

  private def stageRep(ty: IR.TDef, tm: Tm)(implicit
      fresh: Fresh,
      emit: Emit,
      dm: DataMap
  ): R =
    val (ps, spine) = eta(ty.ps)
    lambdaLift(
      quoteRep(eval0(tm)(Empty))(lvl0, Nil, fresh, dm)
        .apps(spine)
        .lams(ps, IR.TDef(ty.rt))
    )

  private def newFresh(): Fresh =
    var n = 0
    () => {
      val c = n
      n += 1
      c
    }

  private def stageDef(d: Def)(implicit dm: DataMap): List[IR.Def] = d match
    case DDef(x, t, st @ STy(_), v) =>
      implicit val fresh: Fresh = newFresh()
      var n2 = 0
      val nds = ArrayBuffer.empty[RD]
      implicit val emit: Emit = () => {
        val c = n2
        n2 + 1
        (s"$x$$$c", d => { nds += d; () })
      }
      val ty = stageFTy(t)
      val value = stageRep(ty, v)
      val rd = RD.Def(x.expose, false, ty, value)
      (nds.toList ++ List(rd)).map(d => toIRDef(d)(newFresh()))
    case _ => Nil

  def stage(ds: Defs): IR.Defs =
    implicit val dds: DataMap =
      ArrayBuffer.empty[(Val1 => List[List[Val1]], List[List[IR.Ty]])]
    val sds = ds.toList.flatMap(stageDef)
    IR.Defs(
      dds.zipWithIndex.map((cs, i) => IR.DData(s"D$i", cs._2)).toList ++ sds
    )
