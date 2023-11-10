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
    "Array"
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
  def VClass(l: Val1) = VRigid(HPrim(Name("Class")), SApp(SId, l, Expl))
  def VClassLabel(x: String) = VClass(VLabelLit(x))
  val VString = VClassLabel("java.lang.String")

  val VInt = VPrim1(Name("Int"))

  inline def VIO(b: Val1, t: Val1) =
    VRigid(HPrim(Name("IO")), SApp(SApp(SId, b, Impl), t, Expl))

  inline def getPrimTypes(
      inline vappE: (Val1, Val1) => Val1
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
    "Array" -> vpiI("b", VBoxity, b => vfun1(VU0(VVal(b)), VU0(VVal(VBoxed))))
  )

  inline def getPrimEliminators(
      inline vappE: (Val1, Val1) => Val1,
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
      )
  )
