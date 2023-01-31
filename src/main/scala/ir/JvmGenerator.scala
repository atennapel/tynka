package ir

import common.Common.*
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

object JvmGenerator:
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
  private val OBJECT_TYPE: Type = Type.getType("Ljava/lang/Object;")

  private def gen(t: Ty)(implicit ctx: Ctx): Type = t match
    case TUnit       => Type.BOOLEAN_TYPE
    case TBool       => Type.BOOLEAN_TYPE
    case TInt        => Type.INT_TYPE
    case TPair(_, _) => PAIR_TYPE

  private def constantValue(e: Let): Option[Any] = e match
    case Let(Nil, Val(v)) => constantValue(v)
    case _                => None
  private def constantValue(e: Value): Option[Any] = e match
    case BoolLit(b) => Some(b)
    case IntLit(n)  => Some(n)
    case _          => None

  private type Locals = IntMap[Int]
  private type Args = Int

  private def genStaticBlock(
      ds0: Defs
  )(implicit ctx: Ctx, cw: ClassWriter): Unit =
    val ds = ds0.toList.filter {
      case DDef(x, _, rt, Nil, b) if constantValue(b).isEmpty =>
        true
      case _ => false
    }
    if ds.nonEmpty then
      val m = new Method("<clinit>", Type.VOID_TYPE, Nil.toArray)
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(ACC_STATIC, m, null, null, cw)
      implicit val locals: Locals = IntMap.empty
      ds.foreach(d => {
        d match
          case DDef(x, g, rt, Nil, b) =>
            implicit val methodStart = mg.newLabel()
            implicit val args: Args = 0
            gen(b)
            mg.putStatic(ctx.moduleType, x, gen(rt.rt))
          case _ =>
      })
      mg.visitInsn(RETURN)
      mg.endMethod()

  private def gen(d: Def)(implicit cw: ClassWriter, ctx: Ctx): Unit = d match
    case DDef(x, g, rt, Nil, v) =>
      cw.visitField(
        (if g then ACC_PRIVATE + ACC_SYNTHETIC
         else ACC_PUBLIC) + ACC_FINAL + ACC_STATIC,
        x,
        gen(rt.rt).getDescriptor,
        null,
        constantValue(v).orNull
      )
    case DDef(x, g, rt, ps, v) =>
      val m = new Method(
        x.toString,
        gen(rt.rt),
        rt.ps.map(gen).toList.toArray
      )
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(
          (if g then ACC_PRIVATE + ACC_SYNTHETIC else ACC_PUBLIC) + ACC_STATIC,
          m,
          null,
          null,
          cw
        )
      implicit val args: Args = ps.size
      implicit val locals: Locals = IntMap.empty
      implicit val methodStart = mg.newLabel()
      mg.visitLabel(methodStart)
      gen(v)
      mg.returnValue()
      mg.endMethod()

  private def gen(
      t: Let
  )(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      args: Args,
      locals: Locals,
      methodStart: Label
  ): Unit = t match
    case Let(ps, b) =>
      val newlocals = ps.foldLeft(locals) { case (locals, (x, ty, v)) =>
        val vr = mg.newLocal(gen(ty))
        gen(v)
        mg.storeLocal(vr)
        locals + (x -> vr)
      }
      gen(b)(mg, ctx, args, newlocals, methodStart)

  private def gen(
      comp: Comp
  )(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      args: Args,
      locals: Locals,
      methodStart: Label
  ): Unit = comp match
    case Val(v) => gen(v)

    case GlobalApp(x, TDef(ps, rt), true, as) =>
      as.foreach(gen)
      Range.inclusive(args - 1, 0, -1).foreach(i => mg.storeArg(i))
      mg.visitJumpInsn(GOTO, methodStart)
    case GlobalApp(x, TDef(ps, rt), false, as) =>
      as.foreach(gen)
      mg.invokeStatic(
        ctx.moduleType,
        new Method(x, gen(rt), ps.map(gen).toArray)
      )

    case PrimApp(PIntLeq, List(a, b)) =>
      gen(a); gen(b)
      val skip = mg.newLabel()
      val end = mg.newLabel()
      mg.ifICmp(GeneratorAdapter.LE, skip)
      mg.push(false)
      mg.visitJumpInsn(GOTO, end)
      mg.visitLabel(skip)
      mg.push(true)
      mg.visitLabel(end)
    case PrimApp(PIntSub, List(a, b)) => gen(a); gen(b); mg.visitInsn(ISUB)
    case PrimApp(PIntMul, List(a, b)) => gen(a); gen(b); mg.visitInsn(IMUL)
    case PrimApp(_, _)                => impossible()

    case Fst(ty, v) =>
      gen(v); mg.getField(PAIR_TYPE, "fst", OBJECT_TYPE); mg.unbox(gen(ty))
    case Snd(ty, v) =>
      gen(v); mg.getField(PAIR_TYPE, "snd", OBJECT_TYPE); mg.unbox(gen(ty))

    case If(c, t, f) =>
      val lFalse = new Label
      val lEnd = new Label
      gen(c)
      mg.visitJumpInsn(IFEQ, lFalse)
      gen(t)
      mg.visitJumpInsn(GOTO, lEnd)
      mg.visitLabel(lFalse)
      gen(f)
      mg.visitLabel(lEnd)

  private def gen(
      t: Value
  )(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      args: Args,
      locals: Locals,
      methodStart: Label
  ): Unit = t match
    case Var(x) if x < args => mg.loadArg(x)
    case Var(x)             => mg.loadLocal(locals(x))

    case Global(x, t) => mg.getStatic(ctx.moduleType, x, gen(t))

    case Unit       => mg.push(true)
    case IntLit(v)  => mg.push(v)
    case BoolLit(v) => mg.push(v)

    case Pair(t1, t2, fst, snd) =>
      mg.newInstance(PAIR_TYPE)
      mg.dup()
      gen(fst); box(t1)
      gen(snd); box(t2)
      mg.invokeConstructor(
        PAIR_TYPE,
        new Method(
          "<init>",
          Type.VOID_TYPE,
          List(OBJECT_TYPE, OBJECT_TYPE).toArray
        )
      )

  private def box(t: Ty)(implicit mg: GeneratorAdapter): Unit = t match
    case TInt =>
      mg.invokeStatic(
        Type.getType(classOf[Integer]),
        Method.getMethod("Integer valueOf (int)")
      )
    case TBool => mg.box(Type.BOOLEAN_TYPE)
    case TUnit => mg.box(Type.BOOLEAN_TYPE)
    case _     =>
