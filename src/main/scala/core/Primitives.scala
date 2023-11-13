package core

import common.Common.*
import Syntax.*
import Value.*

object Primitives:
  val allPrims = Set(
    "CV",
    "Comp",
    "Val",
    "elimCV",
    "Boxity",
    "Boxed",
    "Unboxed",
    "elimBoxity",
    "Rep",
    "ByteRep",
    "ShortRep",
    "IntRep",
    "LongRep",
    "FloatRep",
    "DoubleRep",
    "CharRep",
    "BoolRep",
    "elimRep",
    "Label",
    "appendLabel",
    "eqLabel",
    "Class",
    "IO",
    "returnIO",
    "unsafePerformIO",
    "bindIO",
    "Byte",
    "Short",
    "Int",
    "Long",
    "Float",
    "Double",
    "Char",
    "Array",
    "()",
    "[]",
    "BoolM",
    "TrueM",
    "FalseM",
    "elimBoolM",
    "HId",
    "Refl",
    "elimHId",
    "IFixM",
    "IInM",
    "elimIFixM"
  )

  val CV1 = Prim1(Name("CV"))
  inline def Val(lev: Ty) = App1(Prim1(Name("Val")), lev, Expl)
  val Comp = Prim1(Name("Comp"))
  val VCV1 = VPrim1(Name("CV"))
  val VComp = VPrim1(Name("Comp"))
  inline def VVal(boxity: Val1) =
    VRigid(HPrim(Name("Val")), SApp(SId, boxity, Expl))

  val Boxed = Prim1(Name("Boxed"))
  def Unboxed(rep: Tm1) = App1(Prim1(Name("Unboxed")), rep, Expl)
  val VBoxity = VPrim1(Name("Boxity"))
  val VBoxed = VPrim1(Name("Boxed"))
  inline def VUnboxed(rep: Val1) =
    VRigid(HPrim(Name("Unboxed")), SApp(SId, rep, Expl))

  val VRep = VPrim1(Name("Rep"))
  val VBoolRep = VPrim1(Name("BoolRep"))
  val BoolRep = Prim1(Name("BoolRep"))
  val VCharRep = VPrim1(Name("CharRep"))
  val VByteRep = VPrim1(Name("ByteRep"))
  val ByteRep = Prim1(Name("ByteRep"))
  val VShortRep = VPrim1(Name("ShortRep"))
  val ShortRep = Prim1(Name("ShortRep"))
  val VIntRep = VPrim1(Name("IntRep"))
  val IntRep = Prim1(Name("IntRep"))
  val VLongRep = VPrim1(Name("LongRep"))
  val VFloatRep = VPrim1(Name("FloatRep"))
  val VDoubleRep = VPrim1(Name("DoubleRep"))

  val VLabel = VPrim1(Name("Label"))
  object VAppendLabel:
    def apply(l1: Val1, l2: Val1): Val1 =
      VRigid(HPrim(Name("appendLabel")), SApp(SApp(SId, l1, Expl), l2, Expl))
    def unapply(value: Val1): Option[(Val1, Val1)] = value match
      case VRigid(
            HPrim(Name("appendLabel")),
            SApp(SApp(SId, l1, Expl), l2, Expl)
          ) =>
        Some((l1, l2))
      case _ => None
  object VEqLabel:
    def apply(l1: Val1, l2: Val1): Val1 =
      VRigid(HPrim(Name("eqLabel")), SApp(SApp(SId, l1, Expl), l2, Expl))
    def unapply(value: Val1): Option[(Val1, Val1)] = value match
      case VRigid(
            HPrim(Name("eqLabel")),
            SApp(SApp(SId, l1, Expl), l2, Expl)
          ) =>
        Some((l1, l2))
      case _ => None

  inline def VClass(l: Val1) = VRigid(HPrim(Name("Class")), SApp(SId, l, Expl))
  inline def VClassLabel(x: String) = VClass(VLabelLit(x))
  val VString = VClassLabel("java.lang.String")

  val VInt = VPrim1(Name("Int"))

  inline def VIO(b: Val1, t: Val1) =
    VRigid(HPrim(Name("IO")), SApp(SApp(SId, b, Impl), t, Expl))

  val VUnitType = VPrim1(Name("()"))
  val VBoolM = VPrim1(Name("BoolM"))
  val VTrueM = VPrim1(Name("TrueM"))
  val VFalseM = VPrim1(Name("FalseM"))

  inline def VHId(a: Val1, b: Val1, x: Val1, y: Val1) = VRigid(
    HPrim(Name("HId")),
    SApp(SApp(SApp(SApp(SId, a, Impl), b, Impl), x, Expl), y, Expl)
  )
  inline def VRefl(a: Val1, x: Val1) =
    VRigid(HPrim(Name("Refl")), SApp(SApp(SId, a, Impl), x, Impl))

  inline def VIFixM(ii: Val1, f: Val1, i: Val1) =
    VRigid(
      HPrim(Name("IFixM")),
      SApp(SApp(SApp(SId, ii, Impl), f, Expl), i, Expl)
    )
  inline def VIFixM1(ii: Val1, f: Val1) =
    VRigid(
      HPrim(Name("IFixM")),
      SApp(SApp(SId, ii, Impl), f, Expl)
    )
  inline def VIInM(ii: Val1, f: Val1, i: Val1, x: Val1) =
    VRigid(
      HPrim(Name("IInM")),
      SApp(SApp(SApp(SApp(SId, ii, Impl), f, Impl), i, Impl), x, Expl)
    )

  inline def getPrimTypes(
      inline vappE: (Val1, Val1) => Val1,
      inline vappI: (Val1, Val1) => Val1
  ): Map[String, VTy] = Map(
    "Label" -> VU1,
    "Class" -> vfun1(VLabel, VU0(VVal(VBoxed))),
    "IO" -> vpiI("b", VBoxity, b => vfun1(VU0(VVal(b)), VU0(VComp))),
    "returnIO" ->
      // {b : Boxity} {A : Ty (Val b)} -> ^A -> ^(IO {b} A)
      vpiI(
        "b",
        VBoxity,
        b =>
          vpiI(
            "A",
            VU0(VVal(b)),
            a => vfun1(VLift(VVal(b), a), VLift(VComp, VIO(b, a)))
          )
      ),
    "unsafePerformIO" ->
      // {b : Boxity} {A : Ty (Val b)} -> ^(IO {b} A) -> ^A
      vpiI(
        "b",
        VBoxity,
        b =>
          vpiI(
            "A",
            VU0(VVal(b)),
            a => vfun1(VLift(VComp, VIO(b, a)), VLift(VVal(b), a))
          )
      ),
    "bindIO" ->
      // {b1 b2 : Boxity} {A : Ty (Val b1)} {B : Ty (Val b2)} -> ^(IO {b1} A) -> (^A -> ^(IO {b2} B)) -> ^(IO {b2} B)
      vpiI(
        "b1",
        VBoxity,
        b1 =>
          vpiI(
            "b2",
            VBoxity,
            b2 =>
              vpiI(
                "A",
                VU0(VVal(b1)),
                a =>
                  vpiI(
                    "B",
                    VU0(VVal(b2)),
                    b =>
                      vfun1(
                        VLift(VComp, VIO(b1, a)),
                        vfun1(
                          vfun1(VLift(VVal(b1), a), VLift(VComp, VIO(b2, b))),
                          VLift(VComp, VIO(b2, b))
                        )
                      )
                  )
              )
          )
      ),
    "Rep" -> VU1,
    "ByteRep" -> VRep,
    "ShortRep" -> VRep,
    "IntRep" -> VRep,
    "LongRep" -> VRep,
    "FloatRep" -> VRep,
    "DoubleRep" -> VRep,
    "CharRep" -> VRep,
    "BoolRep" -> VRep,
    "elimRep" ->
      /*
        (P : Rep -> Meta) (rep : Rep)
        (BoolRep : P BoolRep)
        (CharRep : P CharRep)
        (ByteRep : P ByteRep)
        (ShortRep : P ShortRep)
        (IntRep : P IntRep)
        (LongRep : P LongRep)
        (FloatRep : P FloatRep)
        (DoubleRep : P DoubleRep)
        -> P rep
       */
      vpi(
        "P",
        vfun1(VRep, VU1),
        p =>
          vpi(
            "rep",
            VRep,
            rep =>
              vpi(
                "BoolRep",
                vappE(p, VBoolRep),
                _ =>
                  vpi(
                    "CharRep",
                    vappE(p, VCharRep),
                    _ =>
                      vpi(
                        "ByteRep",
                        vappE(p, VByteRep),
                        _ =>
                          vpi(
                            "ShortRep",
                            vappE(p, VShortRep),
                            _ =>
                              vpi(
                                "IntRep",
                                vappE(p, VIntRep),
                                _ =>
                                  vpi(
                                    "LongRep",
                                    vappE(p, VLongRep),
                                    _ =>
                                      vpi(
                                        "FloatRep",
                                        vappE(p, VFloatRep),
                                        _ =>
                                          vpi(
                                            "DoubleRep",
                                            vappE(p, VDoubleRep),
                                            _ => vappE(p, rep)
                                          )
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
          )
      ),
    "Boxity" -> VU1,
    "Boxed" -> VBoxity,
    "Unboxed" -> vfun1(VRep, VBoxity),
    "elimBoxity" ->
      // (P : Boxity -> Meta) (boxity : Boxity) (Boxed : P Boxed) (Unboxed : (rep : Rep) -> P (Unboxed rep)) -> P boxity
      vpi(
        "P",
        vfun1(VBoxity, VU1),
        p =>
          vpi(
            "boxity",
            VBoxity,
            boxity =>
              vpi(
                "Boxed",
                vappE(p, VBoxed),
                _ =>
                  vpi(
                    "Unboxed",
                    vpi("rep", VRep, rep => vappE(p, VUnboxed(rep))),
                    _ => vappE(p, boxity)
                  )
              )
          )
      ),
    "CV" -> VU1,
    "Comp" -> VCV1,
    "Val" -> vfun1(VBoxity, VCV1),
    "elimCV" ->
      // (P : CV -> Meta) (cv : CV) (Comp : P Comp) (Val : (boxity : Boxity) -> P (Val boxity)) -> P cv
      vpi(
        "P",
        vfun1(VCV1, VU1),
        p =>
          vpi(
            "cv",
            VCV1,
            cv =>
              vpi(
                "Comp",
                vappE(p, VComp),
                _ =>
                  vpi(
                    "Val",
                    vpi("boxity", VBoxity, boxity => vappE(p, VVal(boxity))),
                    _ => vappE(p, cv)
                  )
              )
          )
      ),
    "Byte" -> VU0(VVal(VUnboxed(VByteRep))),
    "Short" -> VU0(VVal(VUnboxed(VShortRep))),
    "Int" -> VU0(VVal(VUnboxed(VIntRep))),
    "Long" -> VU0(VVal(VUnboxed(VLongRep))),
    "Float" -> VU0(VVal(VUnboxed(VFloatRep))),
    "Double" -> VU0(VVal(VUnboxed(VDoubleRep))),
    "Char" -> VU0(VVal(VUnboxed(VCharRep))),
    "Array" -> vpiI("b", VBoxity, b => vfun1(VU0(VVal(b)), VU0(VVal(VBoxed)))),
    "()" -> VU1,
    "[]" -> VUnitType,
    "BoolM" -> VU1,
    "TrueM" -> VBoolM,
    "FalseM" -> VBoolM,
    "elimBoolM" ->
      // (P : BoolM -> Meta) (b : BoolM) (TrueM : P TrueM) (FalseM : P FalseM) -> P b
      vpi(
        "P",
        vfun1(VBoolM, VU1),
        p =>
          vpi(
            "b",
            VBoolM,
            b =>
              vpi(
                "TrueM",
                vappE(p, VTrueM),
                _ => vpi("FalseM", vappE(p, VFalseM), _ => vappE(p, b))
              )
          )
      ),
    "HId" -> vpiI("A", VU1, a => vpiI("B", VU1, b => vfun1(a, vfun1(b, VU1)))),
    "Refl" -> vpiI("A", VU1, a => vpiI("x", a, x => VHId(a, a, x, x))),
    "elimHId" ->
      /*
        {A : Meta} {x : A} {y : A}
        (P : {y : A} -> HId {A} {A} x y -> Meta)
        (p : HId {A} {A} x y)
        (Refl : P {x} (Refl {A} {x}))
        -> P {y} p
       */
      vpiI(
        "A",
        VU1,
        a =>
          vpiI(
            "x",
            a,
            x =>
              vpiI(
                "y",
                a,
                y =>
                  vpi(
                    "P",
                    vpiI("y", a, y => vfun1(VHId(a, a, x, y), VU1)),
                    pp =>
                      vpi(
                        "p",
                        VHId(a, a, x, y),
                        p =>
                          vpi(
                            "Refl",
                            vappE(vappI(pp, x), VRefl(a, x)),
                            _ => vappE(vappI(pp, y), p)
                          )
                      )
                  )
              )
          )
      ),
    "IFixM" -> vpiI(
      "I",
      VU1,
      ii => vfun1(vfun1(vfun1(ii, VU1), vfun1(ii, VU1)), vfun1(ii, VU1))
    ),
    "IInM" ->
      // {I : Meta} -> {F : (I -> Meta) -> I -> Meta} -> {i : I} -> F (IFixM {I} F) i -> IFixM {I} F i
      vpiI(
        "I",
        VU1,
        ii =>
          vpiI(
            "F",
            vfun1(vfun1(ii, VU1), vfun1(ii, VU1)),
            f =>
              vpiI(
                "i",
                ii,
                i => vfun1(vappE(vappE(f, VIFixM1(ii, f)), i), VIFixM(ii, f, i))
              )
          )
      ),
    "elimIFixM" ->
      /*
      {I : Meta} {F : (I -> Meta) -> I -> Meta}
      (P : {i : I} -> IFixM {I} F i -> Meta)
      {i : I} (x : IFixM {I} F i)
      (IInM : ({j : I} -> (z : IFixM {I} F j) -> P {j} z) -> {i : I} -> (y : F (IFixM {I} F) i) -> P {i} (IInM {I} {F} {i} y)
      -> P {i} x
       */
      vpiI(
        "I",
        VU1,
        ii =>
          vpiI(
            "F",
            vfun1(vfun1(ii, VU1), vfun1(ii, VU1)),
            f =>
              vpi(
                "P",
                vpiI("i", ii, i => vfun1(VIFixM(ii, f, i), VU1)),
                p =>
                  vpiI(
                    "i",
                    ii,
                    i =>
                      vpi(
                        "x",
                        VIFixM(ii, f, i),
                        x =>
                          vpi(
                            "IInM",
                            vfun1(
                              vpiI(
                                "j",
                                ii,
                                j =>
                                  vpi(
                                    "z",
                                    VIFixM(ii, f, j),
                                    z => vappE(vappI(p, j), z)
                                  )
                              ),
                              vpiI(
                                "i",
                                ii,
                                i =>
                                  vpi(
                                    "y",
                                    vappE(vappE(f, VIFixM1(ii, f)), i),
                                    y => vappE(vappI(p, i), VIInM(ii, f, i, y))
                                  )
                              )
                            ),
                            _ => vappE(vappI(p, i), x)
                          )
                      )
                  )
              )
          )
      ),
    "appendLabel" -> vfun1(VLabel, vfun1(VLabel, VLabel)),
    "eqLabel" -> vfun1(VLabel, vfun1(VLabel, VBoolM))
  )

  inline def getPrimEliminators(
      inline vappE: (Val1, Val1) => Val1,
      inline vappI: (Val1, Val1) => Val1,
      inline vprimelim: (Name, Val1, Int, Icit, List[(Val1, Icit)]) => Val1
  ): Map[String, VTy] = Map(
    "elimRep" ->
      vlam1(
        "P",
        vfun1(VRep, VU1),
        p =>
          vlam1(
            "rep",
            VRep,
            rep =>
              vlam1(
                "BoolRep",
                vappE(p, VBoolRep),
                boolRep =>
                  vlam1(
                    "CharRep",
                    vappE(p, VCharRep),
                    charRep =>
                      vlam1(
                        "ByteRep",
                        vappE(p, VByteRep),
                        byteRep =>
                          vlam1(
                            "ShortRep",
                            vappE(p, VShortRep),
                            shortRep =>
                              vlam1(
                                "IntRep",
                                vappE(p, VIntRep),
                                intRep =>
                                  vlam1(
                                    "LongRep",
                                    vappE(p, VLongRep),
                                    longRep =>
                                      vlam1(
                                        "FloatRep",
                                        vappE(p, VFloatRep),
                                        floatRep =>
                                          vlam1(
                                            "DoubleRep",
                                            vappE(p, VDoubleRep),
                                            doubleRep =>
                                              vprimelim(
                                                Name("elimRep"),
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
      ),
    "elimBoxity" ->
      vlam1(
        "P",
        vfun1(VBoxity, VU1),
        p =>
          vlam1(
            "boxity",
            VBoxity,
            b =>
              vlam1(
                "Boxed",
                vappE(p, VBoxed),
                boxed =>
                  vlam1(
                    "Unboxed",
                    vpi("rep", VRep, rep => vappE(p, VUnboxed(rep))),
                    unboxed =>
                      vprimelim(
                        Name("elimBoxity"),
                        b,
                        1,
                        Expl,
                        List((p, Expl), (boxed, Expl), (unboxed, Expl))
                      )
                  )
              )
          )
      ),
    "elimCV" ->
      vlam1(
        "P",
        vfun1(VCV1, VU1),
        p =>
          vlam1(
            "cv",
            VCV1,
            cv =>
              vlam1(
                "Comp",
                vappE(p, VComp),
                comp =>
                  vlam1(
                    "Val",
                    vpi("boxity", VBoxity, b => vappE(p, VVal(b))),
                    vval =>
                      vprimelim(
                        Name("elimCV"),
                        cv,
                        1,
                        Expl,
                        List((p, Expl), (comp, Expl), (vval, Expl))
                      )
                  )
              )
          )
      ),
    "elimBoolM" ->
      vlam1(
        "P",
        vfun1(VBoolM, VU1),
        p =>
          vlam1(
            "b",
            VBoolM,
            b =>
              vlam1(
                "TrueM",
                vappE(p, VTrueM),
                t =>
                  vlam1(
                    "FalseM",
                    vappE(p, VFalseM),
                    f =>
                      vprimelim(
                        Name("elimBoolM"),
                        b,
                        1,
                        Expl,
                        List((p, Expl), (t, Expl), (f, Expl))
                      )
                  )
              )
          )
      ),
    "elimHId" ->
      vlamI(
        "A",
        VU1,
        a =>
          vlamI(
            "x",
            a,
            x =>
              vlamI(
                "y",
                a,
                y =>
                  vlam1(
                    "P",
                    vpiI("y", a, y => vfun1(VHId(a, a, x, y), VU1)),
                    pp =>
                      vlam1(
                        "p",
                        VHId(a, a, x, y),
                        p =>
                          vlam1(
                            "Refl",
                            vappE(vappI(pp, x), VRefl(a, x)),
                            refl =>
                              vprimelim(
                                Name("elimHId"),
                                refl,
                                4,
                                Expl,
                                List(
                                  (a, Impl),
                                  (x, Impl),
                                  (y, Impl),
                                  (pp, Expl),
                                  (refl, Expl)
                                )
                              )
                          )
                      )
                  )
              )
          )
      ),
    "elimIFixM" ->
      vlamI(
        "I",
        VU1,
        ii =>
          vlamI(
            "F",
            vfun1(vfun1(ii, VU1), vfun1(ii, VU1)),
            f =>
              vlam1(
                "P",
                vpiI("i", ii, i => vfun1(VIFixM(ii, f, i), VU1)),
                p =>
                  vlamI(
                    "i",
                    ii,
                    i =>
                      vlam1(
                        "x",
                        VIFixM(ii, f, i),
                        x =>
                          vlam1(
                            "IInM",
                            vfun1(
                              vpiI(
                                "j",
                                ii,
                                j =>
                                  vpi(
                                    "z",
                                    VIFixM(ii, f, j),
                                    z => vappE(vappI(p, j), z)
                                  )
                              ),
                              vpiI(
                                "i",
                                ii,
                                i =>
                                  vpi(
                                    "y",
                                    vappE(vappE(f, VIFixM1(ii, f)), i),
                                    y => vappE(vappI(p, i), VIInM(ii, f, i, y))
                                  )
                              )
                            ),
                            in =>
                              vprimelim(
                                Name("elimIFixM"),
                                x,
                                4,
                                Expl,
                                List(
                                  (ii, Impl),
                                  (f, Impl),
                                  (p, Expl),
                                  (i, Impl),
                                  (in, Expl)
                                )
                              )
                          )
                      )
                  )
              )
          )
      ),
    "appendLabel" -> vlam1(
      "l1",
      VLabel,
      l1 =>
        vlam1(
          "l2",
          VLabel,
          l2 => vprimelim(Name("appendLabel"), l1, 0, Expl, List((l2, Expl)))
        )
    ),
    "eqLabel" -> vlam1(
      "l1",
      VLabel,
      l1 =>
        vlam1(
          "l2",
          VLabel,
          l2 => vprimelim(Name("eqLabel"), l1, 0, Expl, List((l2, Expl)))
        )
    )
  )
