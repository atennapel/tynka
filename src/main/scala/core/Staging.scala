package core

import common.Common.*
import common.Debug.debug
import common.Ref
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
    case VStringLit1(v: String)
  import Val1.*

  private enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(m: String, x: Name, ty: Val1)
    case VPrim0(x: PrimName)
    case VSplicePrim0(x: PrimName, as: List[Val1])
    case VApp0(f: Val0, a: Val0)
    case VLam0(fnty: Val1, body: Val0 => Val0)
    case VFix0(ty: Val1, rty: Val1, b: (Val0, Val0) => Val0, arg: Val0)
    case VLet0(ty: Val1, bty: Val1, value: Val0, body: Val0 => Val0)
    case VIntLit0(n: Int)
    case VStringLit0(str: String)
    case VCon0(ty: Val1, ix: Int, as: List[Val0])
    case VCase0(ty: Val1, rty: Val1, scrut: Val0, cs: List[Val0])
    case VForeign0(ty: Val1, cmd: String, as: List[(Val0, Val1)])
  import Val0.*

  private def vvar1(ix: Ix)(implicit env: Env): Val1 =
    def go(e: Env, i: Int): Val1 = (e, i) match
      case (Def1(_, v), 0) => v
      case (Def1(e, _), x) => go(e, x - 1)
      case (Def0(e, _), x) => go(e, x - 1)
      case _               => impossible()
    go(env, ix.expose)

  private def vapp1(f: Val1, a: Val1): Val1 = (f, a) match
    case (VLam1(f), _) => f(a)
    case (VPrim1(x, as), _) =>
      (x, as ++ List(a)) match
        case (PEqLabel, List(VStringLit1(a), VStringLit1(b))) =>
          if a == b then VLam1(r => VLam1(a => VLam1(b => a)))
          else VLam1(r => VLam1(a => VLam1(b => b)))
        case (PAppendLabel, List(VStringLit1(a), VStringLit1(b))) =>
          VStringLit1(a + b)
        case _ => VPrim1(x, as ++ List(a))
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
    case Global(m, x)          => eval1(getGlobal(m, x).get.tm)
    case Prim(x)               => VPrim1(x, Nil)
    case Lam(_, _, _, b)       => VLam1(clos1(b))
    case App(f, a, _)          => vapp1(eval1(f), eval1(a))
    case Proj(t, p, _, _)      => vproj1(eval1(t), p)
    case Let(_, _, _, _, v, b) => eval1(b)(Def1(env, eval1(v)))
    case TPair(fst, snd)       => VTPair1(eval1(fst), eval1(snd))
    case Pair(fst, snd, _)     => VPair1(eval1(fst), eval1(snd))
    case TCon(_, cs) =>
      VTCon1(r => cs.map(as => as.map(a => eval1(a)(Def1(env, r)))))
    case Quote(t)     => VQuote1(eval0(t))
    case StringLit(v) => VStringLit1(v)
    case Wk(t)        => eval1(t)(env.tail)

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
    case Var(x)       => vvar0(x)
    case Global(m, x) => VGlobal0(m, x, eval1(getGlobal(m, x).get.ty)(Empty))
    case Prim(x)      => VPrim0(x)
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
    case StringLit(s)   => VStringLit0(s)
    case Con(ty, i, as) => VCon0(eval1(ty), i, as.map(eval0))
    case Case(ty, rty, s, cs) =>
      VCase0(eval1(ty), eval1(rty), eval0(s), cs.map(eval0))
    case Foreign(rt, cmd, as) =>
      val l = eval1(cmd) match
        case VStringLit1(v) => v
        case _              => impossible()
      VForeign0(eval1(rt), l, as.map((a, t) => (eval0(a), eval1(t))))
    case _ => impossible()

  // intermediate rep
  private type RDs = List[RD]

  private enum RD:
    case Def(
        module: IR.GName,
        name: IR.GName,
        gen: Boolean,
        ty: IR.TDef,
        value: R
    )

    override def toString: String = this match
      case Def(m, x, _, t, v) => s"def $m:$x : $t = $v"

  private enum R:
    case Var(name: IR.LName, ty: IR.TDef)
    case Global(m: IR.GName, name: IR.GName, ty: IR.TDef)

    case UnitLit
    case BoolLit(value: Boolean)
    case IntLit(value: Int)
    case StringLit(value: String)

    case App(fn: R, arg: R)
    case PrimApp(name: PrimName, args: List[R])
    case Lam(name: IR.LName, t1: IR.Ty, t2: IR.TDef, body: R)
    case Let(
        name: IR.LName,
        noinline: Boolean,
        ty: IR.TDef,
        bty: IR.TDef,
        value: R,
        body: R
    )

    case Con(ty: IR.GName, ix: Int, as: List[R])
    case Case(ty: IR.GName, rty: IR.TDef, scrut: R, x: IR.LName, cs: List[R])
    case Field(dty: IR.GName, rty: IR.Ty, cix: Int, ix: Int, tm: R)

    case Fix(t1: IR.Ty, t2: IR.TDef, go: IR.LName, x: IR.LName, body: R, arg: R)

    case Box(t: IR.Ty, v: R)
    case Unbox(t: IR.Ty, v: R)

    case Foreign(rt: IR.Ty, cmd: String, as: List[(R, IR.Ty)])

    override def toString: String = this match
      case Var(x, _)       => s"'$x"
      case Global(m, x, _) => s"$m:$x"

      case UnitLit      => "()"
      case IntLit(v)    => s"$v"
      case BoolLit(b)   => if b then "True" else "False"
      case StringLit(s) => s"\"$s\""

      case App(f, a)             => s"($f $a)"
      case PrimApp(p, Nil)       => s"$p"
      case PrimApp(p, as)        => s"($p ${as.mkString(" ")})"
      case Lam(x, t, _, b)       => s"(\\($x : $t). $b)"
      case Let(x, _, t, _, v, b) => s"(let $x : $t = $v; $b)"

      case Con(ty, i, Nil)        => s"(con $ty #$i)"
      case Con(ty, i, as)         => s"(con $ty #$i ${as.mkString(" ")})"
      case Case(ty, _, s, x, Nil) => s"(case $x : $ty = $s)"
      case Case(ty, _, s, x, cs) => s"(case $x : $ty = $s; ${cs.mkString(" ")})"
      case Field(_, _, ci, i, t) => s"(field $ci#$i $t)"

      case Fix(t1, t2, go, x, b, arg) =>
        s"(fix (($go : ${IR.TDef(t1, t2)}) ($x : $t1). $b) $arg)"

      case Box(_, v)   => s"(box $v)"
      case Unbox(_, v) => s"(unbox $v)"

      case Foreign(rt, l, Nil) => s"(foreign $rt $l)"
      case Foreign(rt, l, as) =>
        s"(foreign $rt $l ${as.map(_._1).mkString(" ")})"

    def lams(ps: List[(IR.LName, IR.Ty)], rt: IR.TDef): R =
      ps.foldRight[(R, IR.TDef)]((this, rt)) { case ((x, t), (b, rt)) =>
        (R.Lam(x, t, rt, b), IR.TDef(t, rt))
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
      case Var(x, t)       => List((x, t))
      case Global(_, _, _) => Nil

      case UnitLit      => Nil
      case IntLit(n)    => Nil
      case BoolLit(n)   => Nil
      case StringLit(_) => Nil

      case App(f, a)             => f.fvs ++ a.fvs
      case PrimApp(p, as)        => as.flatMap(_.fvs)
      case Lam(x, _, _, b)       => b.fvs.filterNot((y, _) => y == x)
      case Let(x, _, _, _, v, b) => v.fvs ++ b.fvs.filterNot((y, _) => x == y)

      case Con(_, _, as) => as.flatMap(_.fvs)
      case Case(_, _, s, x, cs) =>
        s.fvs ++ cs.flatMap(_.fvs).filterNot((y, _) => x == y)
      case Field(_, _, _, _, t) => t.fvs

      case Fix(_, _, go, x, b, arg) =>
        b.fvs.filterNot((y, _) => y == go || y == x) ++ arg.fvs

      case Box(_, v)   => v.fvs
      case Unbox(_, v) => v.fvs

      case Foreign(_, _, as) => as.flatMap(_._1.fvs)

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
        case Var(x, _)       => sub.get(x).getOrElse(this)
        case Global(_, _, _) => this

        case UnitLit      => this
        case IntLit(n)    => this
        case BoolLit(n)   => this
        case StringLit(_) => this

        case App(f, a)      => App(f.subst(sub, scope), a.subst(sub, scope))
        case PrimApp(p, as) => PrimApp(p, as.map(_.subst(sub, scope)))
        case Lam(x0, t1, t2, b0) =>
          val (List((x, _)), b) =
            underN(List((x0, IR.TDef(t1))), b0, sub, scope)
          Lam(x, t1, t2, b)
        case Let(x0, ni, t, bt, v, b0) =>
          val (List((x, _)), b) = underN(List((x0, t)), b0, sub, scope)
          Let(x, ni, t, bt, v.subst(sub, scope), b)

        case Con(ty, i, as) => Con(ty, i, as.map(_.subst(sub, scope)))
        case Case(ty, rty, s, x, cs) if scope.contains(x) =>
          val y = scope.max
          val nsub = sub + (x -> Var(y, IR.TDef(IR.TCon(ty))))
          val nscope = scope + y
          Case(ty, rty, s.subst(sub, scope), y, cs.map(_.subst(nsub, nscope)))
        case Case(ty, rty, s, x, cs) =>
          val nsub = sub - x
          val nscope = scope + x
          Case(ty, rty, s.subst(sub, scope), x, cs.map(_.subst(nsub, nscope)))
        case Field(dty, rty, ci, i, t) =>
          Field(dty, rty, ci, i, t.subst(sub, scope))

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

        case Foreign(rt, l, as) =>
          Foreign(rt, l, as.map((a, t) => (a.subst(sub, scope), t)))

  // quotation
  private type DataMap =
    (Ref[Int], ArrayBuffer[(Int, Val1 => List[List[Val1]], List[List[IR.Ty]])])

  private def tyMatch(a: Val1, b: Val1)(implicit l: Int): Boolean = (a, b) match
    case (VPrim1(PTBox, List(_)), VPrim1(PTBox, List(_))) => true
    case (VPrim1(x1, as1), VPrim1(x2, as2))
        if x1 == x2 && as1.size == as2.size =>
      as1.zip(as2).forall(tyMatch)
    case (VTCon1(cs1), VTCon1(cs2))       => dataMatch(cs1, cs2)
    case (VTConName1(x), VTConName1(y))   => x == y
    case (VStringLit1(x), VStringLit1(y)) => x == y
    case _                                => false
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
    dm._2.find((i, cs2, _) => dataMatch(cs, cs2)(0)) match
      case Some(p) => p._1
      case None    => -1

  private def addData(
      cs: Val1 => List[List[Val1]],
      k: (i: Int) => List[List[IR.Ty]]
  )(implicit
      dm: DataMap
  ): Int =
    val ix = findData(cs)
    if ix >= 0 then ix
    else
      val i = dm._1.value
      dm._1.set(i + 1)
      dm._2 += ((i, cs, k(i)))
      i

  private def findOrAddData(cs: Val1 => List[List[Val1]])(implicit
      dm: DataMap
  ): (Int, IR.GName) =
    val i = addData(
      cs,
      i => {
        val x = s"D$i"
        val res = cs(VTConName1(x)).map(as => as.map(quoteVTy))
        res
      }
    )
    (i, s"D$i")

  private def quoteVTy(v: Val1)(implicit dm: DataMap): IR.Ty = v match
    case VTPair1(a, b)          => IR.TCon(findOrAddData(vpairTy1Clos(a, b))._2)
    case VTConName1(x)          => IR.TCon(x)
    case VTCon1(cs)             => IR.TCon(findOrAddData(cs)._2)
    case VPrim1(PTBox, List(_)) => IR.TBox
    case VPrim1(PForeignType, List(VStringLit1(s))) => IR.TForeign(s)
    case _                                          => impossible()

  private def quoteFTy(v: Val1)(implicit dm: DataMap): IR.TDef = v match
    case VPrim1(PTFun, List(a, _, b)) => IR.TDef(quoteVTy(a), quoteFTy(b))
    case VPrim1(PIO, List(t))         => IR.TDef(IR.TUnit, quoteVTy(t))
    case _                            => IR.TDef(quoteVTy(v))

  private type NS = List[(IR.LName, IR.TDef)]
  private type Fresh = () => IR.LName
  private type Emit = () => (IR.GName, IR.GName, RD => Unit)

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
      case VGlobal0(m, x, t) => R.Global(m, x.expose, quoteFTy(t))

      case VIntLit0(v)    => R.IntLit(v)
      case VStringLit0(v) => R.StringLit(v)

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
          false,
          qt,
          quoteFTy(bt),
          quoteRep(v),
          quoteRep(b(VVar0(l)))(l + 1, (x, qt) :: ns, fresh, dm)
        )

      case VCon0(VTCon1(cs), i, as) =>
        R.Con(findOrAddData(cs)._2, i, as.map(quoteRep))
      case VCase0(VTCon1(tcs), rty, scrut, cs) =>
        val qrty = quoteFTy(rty)
        val qscrut = quoteRep(scrut)
        val (ix, dty) = findOrAddData(tcs)
        val qdty = IR.TCon(dty)
        val x = fresh()
        val ecs = dm
          ._2(ix)
          ._3
          .zip(cs)
          .zipWithIndex
          .map { case ((ts, v), ci) =>
            val ps = ts.zipWithIndex.map { case (t, i) =>
              val y = fresh()
              (y, IR.TDef(t), R.Field(dty, t, ci, i, R.Var(x, IR.TDef(qdty))))
            }
            val bodylam =
              quoteRep(v)(l + 1, (x, IR.TDef(qdty)) :: ns, fresh, dm)
            val body = ps.foldLeft(bodylam) { case (f, (x, t, _)) =>
              R.App(f, R.Var(x, t))
            }
            ps.foldRight(body) { case ((x, t, v), b) =>
              R.Let(x, false, t, qrty, v, b)
            }
          }
        R.Case(dty, qrty, qscrut, x, ecs)

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

      case VSplicePrim0(PReturnIO, List(t, v)) =>
        R.Lam(
          fresh(),
          IR.TUnit,
          IR.TDef(quoteVTy(t)),
          quoteRep(vsplice0(v))
        )
      case VSplicePrim0(PRunIO, List(t, v)) =>
        val ta = quoteVTy(t)
        val qv = quoteRep(vsplice0(v))
        R.App(qv, R.UnitLit)
      case VSplicePrim0(PBindIO, List(a, b, c, k)) =>
        val ta = quoteVTy(a)
        val tb = quoteVTy(b)
        val x = fresh()
        val y = fresh()
        val qc = quoteRep(vsplice0(c))
        val qk = quoteRep(vsplice0(vapp1(k, VQuote1(VVar0(l)))))(
          l + 1,
          (y, IR.TDef(ta)) :: ns,
          fresh,
          dm
        )
        R.Lam(
          x,
          IR.TUnit,
          IR.TDef(tb),
          R.Let(
            y,
            true,
            IR.TDef(ta),
            IR.TDef(tb),
            R.App(qc, R.UnitLit),
            R.App(qk, R.UnitLit)
          )
        )

      case VForeign0(ty, cmd, as) =>
        R.Foreign(
          quoteVTy(ty),
          cmd,
          as.map((a, t) => (quoteRep(a), quoteVTy(t)))
        )

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
      case R.Var(_, _)       => true
      case R.Global(_, _, _) => true
      case R.IntLit(_)       => true
      case R.BoolLit(_)      => true
      case R.UnitLit         => true
      case R.StringLit(_)    => true
      case R.Con(_, _, Nil)  => true
      case _                 => false
    def go(tm: R): R =
      tm match
        case R.App(f, a) =>
          go(f) match
            // (let x : t = v; b) a ~> let x : t = v; b a
            case R.Let(x, ni, t, bt, v, b) =>
              go(R.Let(x, ni, t, bt.tail, v, R.App(b, a)))
            // (\(x : t). b) a ~> let x : t = a; b
            case R.Lam(x, t1, t2, b) =>
              go(R.Let(x, false, IR.TDef(t1), t2, a, b))
            case f => R.App(f, go(a))

        case R.PrimApp(p, as) =>
          (p, as.map(go)) match
            case (p, as) => R.PrimApp(p, as)

        case R.Lam(x, t1, t2, b) => R.Lam(x, t1, t2, go(b))

        case R.Let(x, ni, t, bt, v0, b0) =>
          go(v0) match
            case R.Let(y, ni2, t2, bt2, v2, b2) =>
              go(R.Let(y, ni2, t2, bt, v2, R.Let(x, ni, t, bt, b2, b0)))
            case v =>
              val b = go(b0)
              val c = b.fvs.count((y, _) => x == y)
              if !ni && c == 0 then go(b)
              else if !ni && c == 1 || isSmall(v) then go(b.subst(Map(x -> v)))
              else if t.ps.isEmpty then
                val (vs2, spine2) = eta(bt.params)
                R.Let(
                  x,
                  ni,
                  t,
                  IR.TDef(bt.rt),
                  go(v),
                  go(b.apps(spine2))
                ).lams(vs2, IR.TDef(bt.rt))
              else
                val (vs, spine) = eta(t.params)
                val fv = v.fvs
                  .map((x, t) => (x, t.ty))
                  .distinctBy((y, _) => y)
                val nps = fv ++ vs
                val args = nps.zipWithIndex.map { case ((x, _), ix) =>
                  x -> ix
                }.toMap
                val (m, gx, addDef) = emit()
                addDef(
                  RD.Def(
                    m,
                    gx,
                    true,
                    IR.TDef(fv.map(_._2), t),
                    go(v.apps(spine).lams(nps, IR.TDef(t.rt)))
                  )
                )
                val gl = R
                  .Global(m, gx, IR.TDef(nps.map(_._2), t.rt))
                  .apps(fv.map((x, t) => R.Var(x, IR.TDef(t))))
                val (vs2, spine2) = eta(bt.params)
                go(b.subst(Map(x -> gl)).apps(spine2).lams(vs2, IR.TDef(bt.rt)))

        case R.Con(ty, i, as) => R.Con(ty, i, as.map(go))
        case R.Case(ty, rty, scrut, x, cs) =>
          go(scrut) match
            case R.UnitLit        => go(cs(0))
            case R.BoolLit(false) => go(cs(0))
            case R.BoolLit(true)  => go(cs(1))
            case con @ R.Con(_, i, as) =>
              go(R.Let(x, false, IR.TDef(IR.TCon(ty)), rty, con, cs(i)))
            case gscrut =>
              val (vs, spine) = eta(rty.params)
              R
                .Case(
                  ty,
                  IR.TDef(rty.rt),
                  gscrut,
                  x,
                  cs.map(b => go(b.apps(spine)))
                )
                .lams(vs, IR.TDef(rty.rt))
        case R.Field(dty, ty, ci, i, tm) =>
          go(tm) match
            case R.Con(_, _, as) => as(i)
            case tm              => R.Field(dty, ty, ci, i, tm)

        case R.Fix(t1, t2, g, x, b0, arg) =>
          val (vs, spine) = eta(t2.params)
          val fv = b0.fvs
            .filterNot((y, _) => y == g || y == x)
            .map((x, t) => (x, t.ty))
            .distinctBy((y, _) => y)
          val nps = fv ++ List((x, t1)) ++ vs
          val args = nps.zipWithIndex.map { case ((x, _), ix) =>
            x -> ix
          }.toMap
          val (m, gx, addDef) = emit()
          val gl = R
            .Global(m, gx, IR.TDef(nps.map(_._2), t2.rt))
            .apps(fv.map((x, t) => R.Var(x, IR.TDef(t))))
          val b = go(
            b0.apps(spine).lams(nps, IR.TDef(t2.rt)).subst(Map(g -> gl))
          )
          addDef(RD.Def(m, gx, true, IR.TDef(fv.map(_._2) ++ List(t1), t2), b))
          R.App(gl, go(arg))

        case R.Box(t, v) =>
          go(v) match
            case R.Unbox(t, v) => v
            case v             => R.Box(t, v)
        case R.Unbox(t, v) =>
          go(v) match
            case R.Box(t, v) => v
            case v           => R.Unbox(t, v)

        case R.Foreign(rt, l, as) =>
          (l, as.map((a, _) => go(a))) match
            // +
            case ("op:96", List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a + b)
            case ("op:96", List(a, R.IntLit(0)))           => a
            case ("op:96", List(R.IntLit(0), b))           => b
            // -
            case ("op:100", List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a - b)
            case ("op:100", List(R.IntLit(0), b)) =>
              go(R.Foreign(rt, "op:116", List((b, as(1)._2))))
            case ("op:100", List(a, R.IntLit(0))) => go(a)
            // *
            case ("op:104", List(_, R.IntLit(0)))           => R.IntLit(0)
            case ("op:104", List(R.IntLit(0), _))           => R.IntLit(0)
            case ("op:104", List(a, R.IntLit(1)))           => go(a)
            case ("op:104", List(R.IntLit(1), a))           => go(a)
            case ("op:104", List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a * b)
            // /
            case ("op:108", List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a / b)
            case ("op:108", List(a, R.IntLit(1)))           => go(a)
            // %
            case ("op:112", List(R.IntLit(a), R.IntLit(b))) => R.IntLit(a % b)
            case ("op:112", List(a, R.IntLit(1)))           => R.IntLit(0)
            // neg
            case ("op:116", List(R.IntLit(a))) => R.IntLit(-a)
            // ==
            case ("branch:153", List(R.IntLit(a), R.IntLit(b))) =>
              R.BoolLit(a == b)
            // !=
            case ("branch:154", List(R.IntLit(a), R.IntLit(b))) =>
              R.BoolLit(a != b)
            // <
            case ("branch:155", List(R.IntLit(a), R.IntLit(b))) =>
              R.BoolLit(a < b)
            // >
            case ("branch:157", List(R.IntLit(a), R.IntLit(b))) =>
              R.BoolLit(a > b)
            // <=
            case ("branch:158", List(R.IntLit(a), R.IntLit(b))) =>
              R.BoolLit(a <= b)
            // >=
            case ("branch:156", List(R.IntLit(a), R.IntLit(b))) =>
              R.BoolLit(a >= b)

            case (
                  "invokeVirtual:java.lang.String.concat",
                  List(R.StringLit(""), b)
                ) =>
              b
            case (
                  "invokeVirtual:java.lang.String.concat",
                  List(a, R.StringLit(""))
                ) =>
              a
            case (
                  "invokeVirtual:java.lang.String.concat",
                  List(R.StringLit(a), R.StringLit(b))
                ) =>
              R.StringLit(a + b)

            case (l, gas) => R.Foreign(rt, l, gas.zip(as.map(_._2)))

        case tm => tm
    go(tm)

  // to IR
  private type IRNS = Map[IR.LName, IR.LName]
  private def toIR(tm: R, tail: Boolean)(implicit
      ns: IRNS,
      defname: IR.GName,
      fresh: Fresh
  ): IR.Expr = tm match
    case R.Var(x, t)       => IR.Var(ns(x))
    case R.Global(m, x, t) => IR.Global(m, x, t.ty)

    case R.UnitLit      => IR.UnitLit
    case R.IntLit(n)    => IR.IntLit(n)
    case R.BoolLit(b)   => IR.BoolLit(b)
    case R.StringLit(s) => IR.StringLit(s)

    case R.App(f, a) =>
      val (f, as) = tm.flattenApps
      f match
        case R.Global(m, x, t) =>
          IR.GlobalApp(
            m,
            x,
            t,
            tail && x == defname,
            as.map(a => toIR(a, false))
          )
        case _ => impossible()
    case R.PrimApp(p, as)  => IR.PrimApp(p, as.map(a => toIR(a, false)))
    case R.Lam(x, _, _, b) => impossible()
    case R.Let(x, _, t, _, v, b) =>
      val y = fresh()
      IR.Let(
        y,
        b.fvs.exists((z, _) => x == z),
        t.ty,
        toIR(v, false),
        toIR(b, tail)(ns + (x -> y), defname, fresh)
      )

    case R.Con(ty, i, as) => IR.Con(ty, i, as.map(a => toIR(a, false)))
    case R.Case(ty, rty, s, x, cs) =>
      val y = fresh()
      val newns = ns + (x -> y)
      IR.Case(
        ty,
        toIR(s, false),
        y,
        cs.map(c => toIR(c, tail)(newns, defname, fresh))
      )
    case R.Field(dt, t, ci, i, v) => IR.Field(dt, t, ci, i, toIR(v, false))

    case R.Fix(_, _, go, x, b, arg) => ???

    case R.Box(t, v)   => IR.Box(t, toIR(v, false))
    case R.Unbox(t, v) => IR.Unbox(t, toIR(v, false))

    case R.Foreign(rt, l, as) =>
      IR.Foreign(rt, l, as.map((a, t) => (toIR(a, false), t)))

  private def toIRDef(d: RD)(implicit fresh: Fresh): IR.Def = d match
    case RD.Def(m, x, gen, t, v0) =>
      val (ps, _, v) = v0.flattenLams
      implicit val irns: IRNS = ps.map((x, _) => (x, fresh())).toMap
      implicit val defname: IR.GName = x
      IR.DDef(m, x, gen, t, ps.map((x, t) => (irns(x), t)), toIR(v, true))

  // staging
  private def stageFTy(t: Ty)(implicit dm: DataMap): IR.TDef =
    quoteFTy(eval1(t)(Empty))

  private def stageRep(ty: IR.TDef, tm: Tm)(implicit
      fresh: Fresh,
      emit: Emit,
      dm: DataMap
  ): R =
    val (ps, spine) = eta(ty.params)
    val quoted = quoteRep(eval0(tm)(Empty))(lvl0, Nil, fresh, dm)
      .apps(spine)
      .lams(ps, IR.TDef(ty.rt))
    val lifted = lambdaLift(quoted)
    lifted

  private def newFresh(): Fresh =
    var n = 0
    () => {
      val c = n
      n += 1
      c
    }

  private def stageDef(module: String, d: Def)(implicit
      dm: DataMap
  ): List[IR.Def] = d match
    case DDef(m, x, t, st @ STy(_), v) =>
      implicit val fresh: Fresh = newFresh()
      var n2 = 0
      val nds = ArrayBuffer.empty[RD]
      implicit val emit: Emit = () => {
        val c = n2
        n2 += 1
        (module, s"$x$$$c", d => { nds += d; () })
      }
      val ty = stageFTy(t)
      val value = stageRep(ty, v)
      val rd = RD.Def(m, x.expose, false, ty, value)
      (nds.toList ++ List(rd)).map(d => toIRDef(d)(newFresh()))
    case _ => Nil

  def stage(module: String, ds: Defs): IR.Defs =
    implicit val dds: DataMap =
      (
        Ref(0),
        ArrayBuffer.empty[(Int, Val1 => List[List[Val1]], List[List[IR.Ty]])]
      )
    val sds = ds.toList.flatMap(d => stageDef(module, d))
    IR.Defs(
      dds._2.map((i, _, cs) => IR.DData(s"D$i", cs)).toList ++ sds
    )
