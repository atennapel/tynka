package jvmir

import ir.Syntax.{GName, Op}
import ir.Syntax.Op.*
import common.Common.impossible
import common.Debug.debug
import Syntax.*

import org.objectweb.asm.*
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.commons.*

import scala.collection.mutable
import scala.collection.immutable.IntMap

import java.util.function.Function
import java.lang.invoke.LambdaMetafactory
import java.lang.reflect.Modifier
import java.lang.invoke.MethodType
import java.lang.invoke.MethodHandles

import java.io.BufferedOutputStream
import java.io.FileOutputStream

object Generator:
  // from https://stackoverflow.com/questions/8104479/how-to-find-the-longest-common-prefix-of-two-strings-in-scala
  private def longestCommonPrefix(a: String, b: String): String = {
    var same = true
    var i = 0
    while same && i < math.min(a.length, b.length) do
      if a.charAt(i) != b.charAt(i) then same = false
      else i += 1
    a.substring(0, i)
  }

  private final case class Ctx(moduleGName: String, moduleType: Type)

  private val tcons: mutable.Map[GName, Type] = mutable.Map.empty
  private val tconTypes: mutable.Map[GName, String] = mutable.Map.empty

  def generate(moduleGName: String, ds: Defs): Unit =
    implicit val cw: ClassWriter = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    ) {
      override protected def getCommonSuperClass(
          type1: String,
          type2: String
      ): String =
        val prefix = longestCommonPrefix(type1, type2)
        val ret = if prefix.endsWith("$") then prefix.init else prefix
        debug(s"getCommonSuperClass $type1 $type2 $prefix $ret")
        ret
    }
    cw.visit(V1_8, ACC_PUBLIC, moduleGName, null, "java/lang/Object", null)

    implicit val ctx: Ctx = Ctx(moduleGName, Type.getType(s"L$moduleGName;"))

    // empty constructor
    val con = cw.visitMethod(ACC_PRIVATE, "<init>", "()V", null, null)
    con.visitVarInsn(ALOAD, 0)
    con.visitMethodInsn(
      INVOKESPECIAL,
      "java/lang/Object",
      "<init>",
      "()V",
      false
    )
    con.visitInsn(RETURN)
    con.visitMaxs(1, 1)
    con.visitEnd()

    // main method
    val m = new Method(
      "main",
      Type.VOID_TYPE,
      List(Type.getType("[Ljava/lang/String;")).toArray
    )
    val main: GeneratorAdapter =
      new GeneratorAdapter(ACC_PUBLIC + ACC_STATIC, m, null, null, cw)
    main.visitFieldInsn(
      GETSTATIC,
      "java/lang/System",
      "out",
      "Ljava/io/PrintStream;"
    )
    main.push(0)
    main.invokeStatic(
      ctx.moduleType,
      new Method("main", Type.INT_TYPE, List(Type.INT_TYPE).toArray)
    )
    main.invokeStatic(
      Type.getType(classOf[Integer]),
      Method.getMethod("Integer valueOf (int)")
    )
    main.invokeVirtual(
      Type.getType(classOf[Object]),
      Method.getMethod("String toString ()")
    )
    main.visitMethodInsn(
      INVOKEVIRTUAL,
      "java/io/PrintStream",
      "println",
      "(Ljava/lang/String;)V",
      false
    )
    main.visitInsn(RETURN)
    main.visitMaxs(3, 1)
    main.visitEnd

    // generate definitions
    ds.toList.foreach(gen)

    // generate static block
    genStaticBlock(ds)

    // end
    cw.visitEnd()
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$moduleGName.class")
    )
    bos.write(cw.toByteArray())
    bos.close()

  private val PAIR_TYPE: Type = Type.getType("Ljvmstd/Pair;")
  private val EITHER_TYPE: Type = Type.getType("Ljvmstd/Either;")
  private val LIST_TYPE: Type = Type.getType("Ljvmstd/List;")
  private val CONS_TYPE: Type = Type.getType("Ljvmstd/List$Cons;")
  private val OBJECT_TYPE: Type = Type.getType("Ljava/lang/Object;")
  private val LEFT_TYPE: Type = Type.getType("Ljvmstd/Either$Left;")
  private val RIGHT_TYPE: Type = Type.getType("Ljvmstd/Either$Right;")

  private def gen(t: Ty)(implicit ctx: Ctx): Type = t match
    case TBool   => Type.BOOLEAN_TYPE
    case TInt    => Type.INT_TYPE
    case TPair   => PAIR_TYPE
    case TEither => EITHER_TYPE
    case TList   => LIST_TYPE

  private def constantValue(e: Tm): Option[Any] = e match
    case True      => Some(true)
    case False     => Some(false)
    case IntLit(n) => Some(n)
    case _         => None

  private type Locals = IntMap[Int]

  private def genStaticBlock(
      ds0: Defs
  )(implicit ctx: Ctx, cw: ClassWriter): Unit =
    val ds = ds0.toList.filter {
      case DDef(x, _, Nil, rt, b) if constantValue(b).isEmpty => true
      case _                                                  => false
    }
    if ds.nonEmpty then
      val m = new Method("<clinit>", Type.VOID_TYPE, Nil.toArray)
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(ACC_STATIC, m, null, null, cw)
      implicit val locals: Locals = IntMap.empty
      ds.foreach(d => {
        d match
          case DDef(x, g, Nil, rt, b) =>
            implicit val methodStart = mg.newLabel()
            gen(b)
            mg.putStatic(ctx.moduleType, x, gen(rt))
          case _ =>
      })
      mg.visitInsn(RETURN)
      mg.endMethod()

  private def gen(d: Def)(implicit cw: ClassWriter, ctx: Ctx): Unit = d match
    case DDef(x, g, Nil, rt, v) =>
      cw.visitField(
        (if g then ACC_PRIVATE + ACC_SYNTHETIC
         else ACC_PUBLIC) + ACC_FINAL + ACC_STATIC,
        x,
        gen(rt).getDescriptor,
        null,
        constantValue(v).orNull
      )
    case DDef(x, g, ps, rt, v) =>
      val m = new Method(
        x.toString,
        gen(rt),
        ps.map(gen).toList.toArray
      )
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(
          (if g then ACC_PRIVATE + ACC_SYNTHETIC else ACC_PUBLIC) + ACC_STATIC,
          m,
          null,
          null,
          cw
        )
      implicit val locals: Locals = IntMap.empty
      implicit val methodStart = mg.newLabel()
      mg.visitLabel(methodStart)
      gen(v)
      mg.returnValue()
      mg.endMethod()

  private def gen(
      t: Tm
  )(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      locals: Locals,
      methodStart: Label
  ): Unit =
    t match
      case Absurd(t) =>
        t match
          case TBool => mg.push(false)
          case TInt  => mg.push(0)
          case _     => mg.visitInsn(ACONST_NULL)

      case Arg(ix, ty) => mg.loadArg(ix)

      case Global(x, _, TDef(Nil, rt), Nil) =>
        mg.getStatic(ctx.moduleType, x, gen(rt))
      case Global(x, true, TDef(ps, rt), as) =>
        if ps.size != as.size then impossible()
        as.foreach(gen)
        Range.inclusive(as.size - 1, 0, -1).foreach(i => mg.storeArg(i))
        mg.visitJumpInsn(GOTO, methodStart)
      case Global(x, false, TDef(ps, rt), as) =>
        if ps.size != as.size then impossible()
        as.foreach(gen)
        mg.invokeStatic(
          ctx.moduleType,
          new Method(x, gen(rt), ps.map(gen).toArray)
        )

      case Local(x, ty) => mg.loadLocal(locals(x))
      case Let(x, ty, v, b) =>
        val vr = mg.newLocal(gen(ty))
        gen(v)
        mg.storeLocal(vr)
        gen(b)(mg, ctx, locals + (x -> vr), methodStart)

      case Pair(fst, snd) =>
        mg.newInstance(PAIR_TYPE)
        mg.dup()
        gen(fst)
        gen(snd)
        mg.invokeConstructor(
          PAIR_TYPE,
          new Method(
            "<init>",
            Type.VOID_TYPE,
            List(OBJECT_TYPE, OBJECT_TYPE).toArray
          )
        )
      case Fst(tm)       => gen(tm); mg.getField(PAIR_TYPE, "fst", OBJECT_TYPE)
      case Snd(tm)       => gen(tm); mg.getField(PAIR_TYPE, "snd", OBJECT_TYPE)
      case Box(ty, tm)   => gen(tm); box(ty)
      case Unbox(ty, tm) => gen(tm); mg.unbox(gen(ty))

      case NilL(t) => mg.getStatic(LIST_TYPE, "NIL", LIST_TYPE)
      case ConsL(t, hd, tl) =>
        mg.newInstance(CONS_TYPE)
        mg.dup()
        gen(hd)
        gen(tl)
        mg.invokeConstructor(
          CONS_TYPE,
          new Method(
            "<init>",
            Type.VOID_TYPE,
            List(OBJECT_TYPE, LIST_TYPE).toArray
          )
        )
      case CaseL(s, et, nil, hd, tl, cons) =>
        val lEnd = mg.newLabel()
        val lElse = mg.newLabel()
        gen(s)
        mg.dup()
        mg.getStatic(LIST_TYPE, "NIL", LIST_TYPE)
        mg.ifCmp(LIST_TYPE, GeneratorAdapter.EQ, lElse)
        mg.checkCast(CONS_TYPE)
        mg.dup()
        mg.getField(CONS_TYPE, "head", OBJECT_TYPE)
        val get = gen(et)
        mg.unbox(get)
        val lhd = mg.newLocal(get)
        mg.storeLocal(lhd)
        mg.getField(CONS_TYPE, "tail", LIST_TYPE)
        val ltl = mg.newLocal(LIST_TYPE)
        mg.storeLocal(ltl)
        gen(cons)(mg, ctx, locals + (hd -> lhd) + (tl -> ltl), methodStart)
        mg.visitJumpInsn(GOTO, lEnd)
        mg.visitLabel(lElse)
        mg.pop()
        gen(nil)
        mg.visitLabel(lEnd)

      case LeftE(_, _, x) =>
        mg.newInstance(LEFT_TYPE)
        mg.dup()
        gen(x)
        mg.invokeConstructor(
          LEFT_TYPE,
          new Method(
            "<init>",
            Type.VOID_TYPE,
            List(OBJECT_TYPE).toArray
          )
        )
      case RightE(_, _, x) =>
        mg.newInstance(RIGHT_TYPE)
        mg.dup()
        gen(x)
        mg.invokeConstructor(
          RIGHT_TYPE,
          new Method(
            "<init>",
            Type.VOID_TYPE,
            List(OBJECT_TYPE).toArray
          )
        )
      case CaseE(t1, t2, s, x, l, y, r) =>
        val lEnd = mg.newLabel()
        val lElse = mg.newLabel()
        gen(s)
        mg.dup()
        mg.instanceOf(LEFT_TYPE)
        mg.visitJumpInsn(IFEQ, lElse)

        mg.checkCast(LEFT_TYPE)
        mg.getField(LEFT_TYPE, "value", OBJECT_TYPE)
        val get = gen(t1)
        mg.unbox(get)
        val lvalue = mg.newLocal(get)
        mg.storeLocal(lvalue)
        gen(l)(mg, ctx, locals + (x -> lvalue), methodStart)
        mg.visitJumpInsn(GOTO, lEnd)

        mg.visitLabel(lElse)
        mg.checkCast(RIGHT_TYPE)
        mg.getField(RIGHT_TYPE, "value", OBJECT_TYPE)
        val get2 = gen(t2)
        mg.unbox(get2)
        val lvalue2 = mg.newLocal(get2)
        mg.storeLocal(lvalue2)
        gen(r)(mg, ctx, locals + (y -> lvalue2), methodStart)

        mg.visitLabel(lEnd)

      case True  => mg.push(true)
      case False => mg.push(false)
      case If(t, c, a, b) =>
        val lFalse = new Label
        val lEnd = new Label
        gen(c)
        mg.visitJumpInsn(IFEQ, lFalse)
        gen(a)
        mg.visitJumpInsn(GOTO, lEnd)
        mg.visitLabel(lFalse)
        gen(b)
        mg.visitLabel(lEnd)

      case IntLit(n) => mg.push(n)
      case Binop(op, a, b) =>
        gen(a)
        gen(b)
        op match
          case BAdd => mg.visitInsn(IADD)
          case BMul => mg.visitInsn(IMUL)
          case BSub => mg.visitInsn(ISUB)
          case BDiv => mg.visitInsn(IDIV)
          case BMod => mg.visitInsn(IREM)
          case BEq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.EQ, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case BNeq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.NE, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case BLt =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.LT, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case BGt =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.GT, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case BLeq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.LE, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case BGeq =>
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(GeneratorAdapter.GE, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)

  private def box(t: Ty)(implicit mg: GeneratorAdapter): Unit = t match
    case TInt =>
      mg.invokeStatic(
        Type.getType(classOf[Integer]),
        Method.getMethod("Integer valueOf (int)")
      )
    case _ =>
