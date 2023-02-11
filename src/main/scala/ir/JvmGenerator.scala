package ir

import common.Common.*
import common.Debug.debug
import Syntax.*

import org.objectweb.asm.*
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.commons.*

import scala.collection.mutable
import scala.collection.immutable.IntMap
import scala.annotation.tailrec

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

  private enum DataKind:
    case VoidLike
    case UnitLike
    case BoolLike
    case FiniteLike(n: Int)
    case ProductLike(ts: List[Ty])
    case NewtypeLike(t: Ty)
    case ADT
  import DataKind.*

  private final case class Ctx(moduleName: String, moduleType: Type)
  private val tcons: mutable.Map[GName, (Type, DataKind)] = mutable.Map.empty
  private val cons: mutable.Map[GName, mutable.Map[Int, (Type, List[Ty])]] =
    mutable.Map.empty

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

  private val OBJECT_TYPE: Type = Type.getType("Ljava/lang/Object;")

  private def gen(t: Ty)(implicit ctx: Ctx): Type = t match
    case TUnit => Type.BOOLEAN_TYPE
    case TBool => Type.BOOLEAN_TYPE
    case TInt  => Type.INT_TYPE
    case TCon(x) =>
      val (t, k) = tcons(x)
      k match
        case UnitLike       => Type.BOOLEAN_TYPE
        case BoolLike       => Type.BOOLEAN_TYPE
        case VoidLike       => Type.BOOLEAN_TYPE
        case FiniteLike(_)  => Type.INT_TYPE
        case NewtypeLike(t) => gen(t)
        case _              => t
    case TBox           => OBJECT_TYPE
    case TForeign(desc) => Type.getType(desc)

  private def constantValue(e: Expr): Option[Any] = e match
    case UnitLit            => Some(false)
    case StringLit(s)       => Some(s)
    case BoolLit(b)         => Some(b)
    case IntLit(n)          => Some(n)
    case Con(_, _, List(v)) => constantValue(v)
    case _                  => None

  private type Locals = IntMap[Int]
  private type Args = Int

  private def genStaticBlock(
      ds0: Defs
  )(implicit ctx: Ctx, cw: ClassWriter): Unit =
    val ds = ds0.toList.filter {
      case DDef(x, _, TDef(None, _), _, b) if constantValue(b).isEmpty =>
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
          case DDef(x, g, TDef(None, rt), _, b) =>
            implicit val methodStart = mg.newLabel()
            implicit val args: Args = 0
            gen(b)
            mg.putStatic(ctx.moduleType, x, gen(rt))
          case _ =>
      })
      mg.visitInsn(RETURN)
      mg.endMethod()

  private def gen(d: Def)(implicit cw: ClassWriter, ctx: Ctx): Unit = d match
    case DDef(x, g, TDef(None, ty), _, v) =>
      cw.visitField(
        (if g then ACC_PRIVATE + ACC_SYNTHETIC
         else ACC_PUBLIC) + ACC_FINAL + ACC_STATIC,
        x,
        gen(ty).getDescriptor,
        null,
        constantValue(v).orNull
      )
    case DDef(x, g, TDef(Some(ts), rt), ps, v) =>
      val m = new Method(
        x.toString,
        gen(rt),
        ts.map(gen).toList.toArray
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
    case DData(x, cs) =>
      val kind = cs match
        case Nil                        => VoidLike
        case List(Nil)                  => UnitLike
        case List(Nil, Nil)             => BoolLike
        case cs if cs.forall(_.isEmpty) => FiniteLike(cs.size)
        case List(List(t))              => NewtypeLike(t)
        case List(ts)                   => ProductLike(ts)
        case _                          => ADT
      tcons += (x -> (Type.getType(s"L${ctx.moduleName}$$$x;"), kind))
      kind match
        case VoidLike        => ()
        case UnitLike        => ()
        case BoolLike        => ()
        case FiniteLike(_)   => ()
        case NewtypeLike(_)  => ()
        case ProductLike(ts) => genProduct(x, ts)
        case _               => genData(x, cs)

  private def genData(dx: GName, cs: List[List[Ty]])(implicit
      cw: ClassWriter,
      ctx: Ctx
  ): Unit =
    val className = s"${ctx.moduleName}$$$dx"
    val datacw = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    )
    datacw.visit(
      V1_8,
      ACC_PUBLIC + ACC_ABSTRACT,
      className,
      null,
      "java/lang/Object",
      null
    )
    // private empty constructor
    val con = datacw.visitMethod(ACC_PROTECTED, "<init>", "()V", null, null)
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
    // datatype constructors
    cs.zipWithIndex.foreach((as, i) => {
      if cons.get(dx).isEmpty then cons(dx) = mutable.Map.empty
      cons(dx) += i -> (Type.getType(s"L$className$$$i;"), as)
      genCon(className, i, as)
      datacw.visitInnerClass(
        s"$className$$$i",
        className,
        s"$$$i",
        ACC_PUBLIC + ACC_STATIC + ACC_FINAL
      )
      if as.isEmpty then
        datacw.visitField(
          ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
          s"$$$i$$",
          s"L$className$$$i;",
          null,
          null
        )
    })
    // 0-ary constructor initialization
    val m = new Method("<clinit>", Type.VOID_TYPE, Nil.toArray)
    implicit val stmg: GeneratorAdapter =
      new GeneratorAdapter(ACC_STATIC, m, null, null, datacw)
    cs.zipWithIndex.foreach((as, i) => {
      if as.isEmpty then
        val conType = Type.getType(s"L$className$$$i;")
        stmg.newInstance(conType)
        stmg.dup()
        stmg.invokeConstructor(
          conType,
          new Method(
            "<init>",
            Type.VOID_TYPE,
            Array.empty
          )
        )
        stmg.putStatic(Type.getType(s"L$className;"), s"$$$i$$", conType)
    })
    stmg.visitInsn(RETURN)
    stmg.endMethod()
    // output
    datacw.visitEnd()
    cw.visitInnerClass(
      className,
      ctx.moduleName,
      dx,
      ACC_PUBLIC + ACC_ABSTRACT + ACC_STATIC
    )
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$className.class")
    )
    bos.write(datacw.toByteArray())
    bos.close()

  private def genCon(superName: String, x: Int, as: List[Ty])(implicit
      ctx: Ctx
  ): Unit =
    val className = s"$superName$$$x"
    val cw = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    )
    cw.visit(
      V1_8,
      ACC_PUBLIC + ACC_STATIC + ACC_FINAL,
      className,
      null,
      superName,
      null
    )
    // fields
    as.zipWithIndex.foreach((ty, i) => {
      cw.visitField(
        ACC_PUBLIC + ACC_FINAL,
        s"a$i",
        gen(ty).getDescriptor,
        null,
        null
      )
    })
    // class constructor
    val m = new Method("<init>", Type.VOID_TYPE, as.map(gen).toArray)
    val mg: GeneratorAdapter =
      new GeneratorAdapter(
        if as.isEmpty then ACC_PROTECTED else ACC_PUBLIC,
        m,
        null,
        null,
        cw
      )
    mg.visitVarInsn(ALOAD, 0)
    mg.visitMethodInsn(
      INVOKESPECIAL,
      superName,
      "<init>",
      "()V",
      false
    )
    as.zipWithIndex.foreach((ty, i) => {
      mg.loadThis()
      mg.loadArg(i)
      mg.putField(Type.getType(s"L$className;"), s"a$i", gen(ty))
    })
    mg.visitInsn(RETURN)
    mg.visitMaxs(1, 1)
    mg.visitEnd()
    // done
    cw.visitEnd()
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$className.class")
    )
    bos.write(cw.toByteArray())
    bos.close()

  private def genProduct(dx: GName, as: List[Ty])(implicit
      ctx: Ctx,
      outercw: ClassWriter
  ): Unit =
    val className = s"${ctx.moduleName}$$$dx"
    val cw = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    )
    cw.visit(
      V1_8,
      ACC_PUBLIC + ACC_STATIC + ACC_FINAL,
      className,
      null,
      "java/lang/Object",
      null
    )
    // fields
    as.zipWithIndex.foreach((ty, i) => {
      cw.visitField(
        ACC_PUBLIC + ACC_FINAL,
        s"a$i",
        gen(ty).getDescriptor,
        null,
        null
      )
    })
    // class constructor
    val m = new Method("<init>", Type.VOID_TYPE, as.map(gen).toArray)
    val mg: GeneratorAdapter =
      new GeneratorAdapter(
        if as.isEmpty then ACC_PROTECTED else ACC_PUBLIC,
        m,
        null,
        null,
        cw
      )
    mg.visitVarInsn(ALOAD, 0)
    mg.visitMethodInsn(
      INVOKESPECIAL,
      "java/lang/Object",
      "<init>",
      "()V",
      false
    )
    as.zipWithIndex.foreach((ty, i) => {
      mg.loadThis()
      mg.loadArg(i)
      mg.putField(Type.getType(s"L$className;"), s"a$i", gen(ty))
    })
    mg.visitInsn(RETURN)
    mg.visitMaxs(1, 1)
    mg.visitEnd()
    // done
    cw.visitEnd()
    outercw.visitInnerClass(
      className,
      ctx.moduleName,
      dx,
      ACC_PUBLIC + ACC_STATIC
    )
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$className.class")
    )
    bos.write(cw.toByteArray())
    bos.close()

  private def gen(
      t: Expr
  )(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      args: Args,
      locals: Locals,
      methodStart: Label
  ): Unit =
    t match
      case Let(x, false, t, v, b) => gen(v); mg.pop(); gen(b)
      case Let(x, _, t, v, b) =>
        val vr = mg.newLocal(gen(t))
        gen(v)
        mg.storeLocal(vr)
        gen(b)(mg, ctx, args, locals + (x -> vr), methodStart)

      case GlobalApp(_, x, TDef(Some(ps), rt), true, as) if x == mg.getName =>
        as.foreach(gen)
        Range.inclusive(args - 1, 0, -1).foreach(i => mg.storeArg(i))
        mg.visitJumpInsn(GOTO, methodStart)
      case GlobalApp(_, x, TDef(Some(ps), rt), _, as) =>
        as.foreach(gen)
        mg.invokeStatic(
          ctx.moduleType,
          new Method(x, gen(rt), ps.map(gen).toArray)
        )
      case GlobalApp(_, _, _, _, _) => impossible()

      case Unbox(t, v) => gen(v); mg.unbox(gen(t))

      case PrimApp(_, _) => impossible()

      case Field(dty, ty, ci, i, v) =>
        val (jty, kind) = tcons(dty)
        kind match
          case VoidLike        => impossible()
          case UnitLike        => impossible()
          case BoolLike        => impossible()
          case FiniteLike(n)   => impossible()
          case NewtypeLike(t)  => gen(v)
          case ProductLike(ts) => gen(v); mg.getField(jty, s"a$i", gen(ty))
          case ADT             => gen(v); mg.getField(jty, s"a$i", gen(ty))

      case Case(ty, scrut, x, cs) =>
        val (jty, kind) = tcons(ty)
        kind match
          case VoidLike =>
            val ty = Type.getType(classOf[Exception])
            mg.newInstance(ty)
            mg.dup()
            gen(scrut)
            mg.invokeVirtual(OBJECT_TYPE, Method.getMethod("String toString()"))
            mg.invokeConstructor(ty, Method.getMethod("void <init> (String)"))
            mg.throwException()
          case UnitLike => gen(scrut); mg.pop(); gen(cs(0))
          case BoolLike =>
            val lFalse = new Label
            val lEnd = new Label
            gen(scrut)
            mg.visitJumpInsn(IFEQ, lFalse)
            gen(cs(1))
            mg.visitJumpInsn(GOTO, lEnd)
            mg.visitLabel(lFalse)
            gen(cs(0))
            mg.visitLabel(lEnd)
          case FiniteLike(k) =>
            if k <= 2 then impossible()
            gen(scrut)
            val labels = (0 until k).map(_ => mg.newLabel())
            mg.visitTableSwitchInsn(0, k - 1, labels.last, labels.toArray*)
            val lEnd = mg.newLabel()
            labels.zipWithIndex.foreach { (l, i) =>
              mg.visitLabel(l)
              gen(cs(i))
              mg.visitJumpInsn(GOTO, lEnd)
            }
            mg.visitLabel(lEnd)
          case NewtypeLike(t) =>
            val local = mg.newLocal(gen(t))
            gen(scrut)
            mg.storeLocal(local)
            gen(cs(0))(mg, ctx, args, locals + (x -> local), methodStart)
          case ProductLike(_) =>
            val local = mg.newLocal(jty)
            gen(scrut)
            mg.storeLocal(local)
            gen(cs(0))(mg, ctx, args, locals + (x -> local), methodStart)
          case _ =>
            gen(scrut)
            val lEnd = new Label
            var lNextCase = new Label
            cs.zipWithIndex.init.foreach { case (b, i) =>
              val condata = cons(ty)(i)
              val contype = condata._1
              val isNilary = condata._2.isEmpty
              mg.visitLabel(lNextCase)
              lNextCase = new Label
              mg.dup()
              if isNilary then
                mg.getStatic(jty, s"$$$i$$", contype)
                mg.visitJumpInsn(IF_ACMPNE, lNextCase)
              else
                mg.instanceOf(contype)
                mg.visitJumpInsn(IFEQ, lNextCase)
              if isNilary then
                mg.pop()
                gen(b)
              else
                mg.checkCast(contype)
                val local = mg.newLocal(contype)
                mg.storeLocal(local)
                gen(b)(mg, ctx, args, locals + (x -> local), methodStart)
              mg.visitJumpInsn(GOTO, lEnd)
            }
            mg.visitLabel(lNextCase)
            val i = cs.size - 1
            val b = cs.last
            val condata = cons(ty)(i)
            val contype = condata._1
            val isNilary = condata._2.isEmpty
            if isNilary then
              mg.pop()
              gen(b)
            else
              mg.checkCast(contype)
              val local = mg.newLocal(contype)
              mg.storeLocal(local)
              gen(b)(mg, ctx, args, locals + (x -> local), methodStart)
            mg.visitLabel(lEnd)

      case Foreign(_, "cast", List((v, _)))       => gen(v)
      case Foreign(_, "returnVoid", List((v, _))) => gen(v)
      case Foreign(_, op, as) if op.startsWith("op:") =>
        op.drop(3).toIntOption match
          case Some(n) => as.foreach((v, _) => gen(v)); mg.visitInsn(n)
          case _       => impossible()
      case Foreign(_, op, as) if op.startsWith("branch:") =>
        op.drop(7).toIntOption match
          case Some(n) =>
            as.foreach((v, _) => gen(v))
            val skip = mg.newLabel()
            val end = mg.newLabel()
            mg.ifICmp(n, skip)
            mg.push(false)
            mg.visitJumpInsn(GOTO, end)
            mg.visitLabel(skip)
            mg.push(true)
            mg.visitLabel(end)
          case _ => impossible()
      case Foreign(rt @ TForeign(_), "instantiate", as) =>
        val ty = gen(rt)
        mg.newInstance(ty)
        mg.dup()
        as.foreach((v, _) => gen(v))
        mg.invokeConstructor(
          ty,
          Method("<init>", Type.VOID_TYPE, as.map((_, t) => gen(t)).toArray)
        )
      case Foreign(rt, cmd0, as) =>
        val s = cmd0.split("\\:")
        val cmd = s.head
        val arg = s.tail.mkString(":")
        (cmd, arg, as) match
          case ("getStatic", arg, Nil) =>
            val ss = arg.split("\\.")
            val owner = s"L${ss.init.mkString("/")};"
            val member = ss.last
            mg.getStatic(Type.getType(owner), member, gen(rt))
          case ("invokeVirtual", arg, as) =>
            val ss = arg.split("\\.")
            val owner = s"L${ss.init.mkString("/")};"
            val member = ss.last
            as.foreach((v, _) => gen(v))
            mg.invokeVirtual(
              Type.getType(owner),
              Method(member, gen(rt), as.tail.map((_, t) => gen(t)).toArray)
            )
          case ("invokeVirtualVoid", arg, as) =>
            val ss = arg.split("\\.")
            val owner = s"L${ss.init.mkString("/")};"
            val member = ss.last
            as.foreach((v, _) => gen(v))
            mg.invokeVirtual(
              Type.getType(owner),
              Method(
                member,
                Type.VOID_TYPE,
                as.tail.map((_, t) => gen(t)).toArray
              )
            )
            mg.push(false)
          case _ => impossible()

      case Var(x) if x < args => mg.loadArg(x)
      case Var(x)             => mg.loadLocal(locals(x))

      case Global(_, x, t) => mg.getStatic(ctx.moduleType, x, gen(t))

      case Box(t, v) => gen(v); mg.box(gen(t))

      case UnitLit      => mg.push(false)
      case IntLit(v)    => mg.push(v)
      case BoolLit(v)   => mg.push(v)
      case StringLit(v) => mg.push(v)

      case Con(ty, i, as) =>
        val (jty, kind) = tcons(ty)
        (kind, as) match
          case (VoidLike, _)       => impossible()
          case (UnitLike, _)       => mg.push(false)
          case (BoolLike, _)       => mg.push(i != 0)
          case (FiniteLike(_), _)  => mg.push(i)
          case (NewtypeLike(_), _) => gen(as.head)
          case (ProductLike(ts), _) =>
            val conType = Type.getType(s"L${ctx.moduleName}$$$ty;")
            mg.newInstance(conType)
            mg.dup()
            as.foreach(gen)
            mg.invokeConstructor(
              conType,
              new Method(
                "<init>",
                Type.VOID_TYPE,
                ts.map(gen).toArray
              )
            )
          case (_, Nil) =>
            val conType = Type.getType(s"L${ctx.moduleName}$$$ty$$$i;")
            mg.getStatic(
              tcons(ty)._1,
              s"$$$i$$",
              conType
            )
          case _ =>
            val conType = Type.getType(s"L${ctx.moduleName}$$$ty$$$i;")
            mg.newInstance(conType)
            mg.dup()
            as.foreach(gen)
            mg.invokeConstructor(
              conType,
              new Method(
                "<init>",
                Type.VOID_TYPE,
                cons(ty)(i)._2.map(gen).toArray
              )
            )
