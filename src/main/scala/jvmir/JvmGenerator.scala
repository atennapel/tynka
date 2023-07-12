package jvmir

import common.Common.*
import common.Debug.debug
import Syntax.*
import JvmName.*

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
  private val OBJECT_TYPE: Type = Type.getType("Ljava/lang/Object;")

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

  private type Locals = IntMap[(Int, Ty)]

  private final case class Ctx(moduleName: String, moduleType: Type)
  private val tcons: mutable.Map[GName, (Type, DataKind, List[GName])] =
    mutable.Map.empty
  private val cons: mutable.Map[GName, mutable.Map[GName, (Type, List[Ty])]] =
    mutable.Map.empty

  private def name(x: GName)(implicit ctx: Ctx): GName = s"${escape(x)}"

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
    cw.visit(
      V1_8,
      ACC_PUBLIC + ACC_FINAL,
      moduleGName,
      null,
      "java/lang/Object",
      null
    )

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
    ds.toList.foreach(prepareData)
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

  private def gen(t: Ty)(implicit ctx: Ctx): Type = t match
    case TForeign(cls) => Type.getType(cls)
    case TCon(x) =>
      val (t, k, _) = tcons(x)
      k match
        case UnitLike       => Type.BOOLEAN_TYPE
        case BoolLike       => Type.BOOLEAN_TYPE
        case VoidLike       => Type.BOOLEAN_TYPE
        case FiniteLike(_)  => Type.INT_TYPE
        case NewtypeLike(t) => gen(t)
        case _              => t

  private def constantValue(e: Tm): Option[Any] = e match
    case IntLit(n)          => Some(n)
    case Con(_, _, List(v)) => constantValue(v)
    case _                  => None

  private val primitives = "BCDFIJSZ".split("")
  private def descriptorIsPrimitive(d: String): Boolean = primitives.contains(d)

  private def isBoxed(t: Ty): Boolean = t match
    case TForeign(d) if descriptorIsPrimitive(d) => false
    case TForeign(_)                             => true
    case TCon(x) =>
      val (_, k, _) = tcons(x)
      k match
        case UnitLike       => false
        case BoolLike       => false
        case VoidLike       => false
        case FiniteLike(_)  => false
        case NewtypeLike(t) => isBoxed(t)
        case ProductLike(_) => true
        case ADT            => true

  private def genStaticBlock(
      ds0: Defs
  )(implicit ctx: Ctx, cw: ClassWriter): Unit =
    val ds = ds0.toList.filter {
      case DDef(x, _, TDef(None, _), b) if constantValue(b).isEmpty =>
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
          case DDef(x, g, TDef(None, rt), b) =>
            implicit val methodStart = mg.newLabel()
            gen(b)
            mg.putStatic(ctx.moduleType, name(x), gen(rt))
          case _ =>
      })
      mg.visitInsn(RETURN)
      mg.endMethod()

  private def prepareData(d: Def)(implicit ctx: Ctx): Unit = d match
    case DData(x, cs) =>
      val kind = cs match
        case Nil                                  => VoidLike
        case List((_, Nil))                       => UnitLike
        case List((_, Nil), (_, Nil))             => BoolLike
        case cs if cs.forall((_, l) => l.isEmpty) => FiniteLike(cs.size)
        case List((_, List(t)))                   => NewtypeLike(t)
        case List(ts)                             => ProductLike(ts._2)
        case _                                    => ADT
      tcons += (x -> (Type.getType(s"L${ctx.moduleName}$$$x;"), kind, cs.map(
        _._1
      )))
    case _ =>

  private def gen(d: Def)(implicit cw: ClassWriter, ctx: Ctx): Unit = d match
    case DDef(x, g, TDef(None, ty), v) =>
      cw.visitField(
        (if g then ACC_PRIVATE + ACC_SYNTHETIC
         else ACC_PUBLIC) + ACC_FINAL + ACC_STATIC,
        name(x),
        gen(ty).getDescriptor,
        null,
        constantValue(v).orNull
      )
    case DDef(x, g, TDef(Some(ts), rt), v) =>
      val m = new Method(
        name(x),
        gen(rt),
        ts.map(gen).toList.toArray
      )
      implicit val mg: GeneratorAdapter =
        new GeneratorAdapter(
          ACC_FINAL + ACC_STATIC + (if g then ACC_PRIVATE + ACC_SYNTHETIC
                                    else ACC_PUBLIC),
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
    case DData(x, cs) =>
      tcons(x)._2 match
        case VoidLike        => ()
        case UnitLike        => ()
        case BoolLike        => ()
        case FiniteLike(_)   => ()
        case NewtypeLike(_)  => ()
        case ProductLike(ts) => genProduct(x, ts)
        case _               => genData(x, cs)

  private def genData(dx: GName, cs: List[(GName, List[Ty])])(implicit
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
    cs.zipWithIndex.foreach { case ((cx, as), i) =>
      val ecx = escape(cx)
      if cons.get(dx).isEmpty then cons(dx) = mutable.Map.empty
      cons(dx) += cx -> (Type.getType(s"L$className$$$ecx;"), as)
      genCon(className, cx, as)
      datacw.visitInnerClass(
        s"$className$$$ecx",
        className,
        s"$$$ecx",
        ACC_PUBLIC + ACC_STATIC + ACC_FINAL
      )
      if as.isEmpty then
        datacw.visitField(
          ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
          s"$$$i$$",
          s"L$className$$$ecx;",
          null,
          null
        )
    }
    // 0-ary constructor initialization
    val m = new Method("<clinit>", Type.VOID_TYPE, Nil.toArray)
    implicit val stmg: GeneratorAdapter =
      new GeneratorAdapter(ACC_STATIC, m, null, null, datacw)
    cs.zipWithIndex.foreach { case ((cx, as), i) =>
      val ecx = escape(cx)
      if as.isEmpty then
        val conType = Type.getType(s"L$className$$$ecx;")
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
        stmg.putStatic(Type.getType(s"L$className;"), s"$$$ecx$$", conType)
    }
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

  private def genCon(superName: String, x: String, as: List[Ty])(implicit
      ctx: Ctx
  ): Unit =
    val className = s"$superName$$${escape(x)}"
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
      t: Tm
  )(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      locals: Locals,
      methodStart: Label
  ): Unit = t match
    case IntLit(v)    => mg.push(v)
    case StringLit(v) => mg.push(v)
    case Arg(ix)      => mg.loadArg(ix)
    case Var(x)       => mg.loadLocal(locals(x)._1)

    case Global(x, t) => mg.getStatic(ctx.moduleType, name(x), gen(t))
    case GlobalApp(x, TDef(Some(ps), rt), true, as) if name(x) == mg.getName =>
      // local clearing to allow gc (taken from Clojure)
      locals.values.foreach { (l, ty) =>
        if isBoxed(ty) then
          mg.visitInsn(Opcodes.ACONST_NULL)
          mg.storeLocal(l)
      }
      as.foreach(gen)
      Range.inclusive(as.size - 1, 0, -1).foreach(i => mg.storeArg(i))
      mg.visitJumpInsn(GOTO, methodStart)
    case GlobalApp(x, TDef(Some(ps), rt), _, as) =>
      as.foreach(gen)
      mg.invokeStatic(
        ctx.moduleType,
        new Method(name(x), gen(rt), ps.map(gen).toArray)
      )
    case GlobalApp(_, _, _, _) => impossible()

    case Let(x, t, v, b) =>
      val vr = mg.newLocal(gen(t))
      gen(v)
      mg.storeLocal(vr)
      gen(b)(mg, ctx, locals + (x -> (vr, t)), methodStart)

    case Con(ty, con, as) =>
      val (jty, kind, cs) = tcons(ty)
      (kind, as) match
        case (VoidLike, _)       => impossible()
        case (UnitLike, _)       => mg.push(false)
        case (BoolLike, _)       => mg.push(cs.indexOf(con) != 0)
        case (FiniteLike(_), _)  => mg.push(cs.indexOf(con))
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
          val conType = Type.getType(s"L${ctx.moduleName}$$$ty$$$con;")
          mg.getStatic(
            tcons(ty)._1,
            s"$$$con$$",
            conType
          )
        case _ =>
          val conType = Type.getType(s"L${ctx.moduleName}$$$ty$$$con;")
          mg.newInstance(conType)
          mg.dup()
          as.foreach(gen)
          mg.invokeConstructor(
            conType,
            new Method(
              "<init>",
              Type.VOID_TYPE,
              cons(ty)(con)._2.map(gen).toArray
            )
          )

    case Field(dty, cx, v, i) =>
      val (jty, kind, _) = tcons(dty)
      kind match
        case VoidLike       => impossible()
        case UnitLike       => impossible()
        case BoolLike       => impossible()
        case FiniteLike(n)  => impossible()
        case NewtypeLike(t) => gen(v)
        case ProductLike(ts) =>
          gen(v); mg.getField(jty, s"a$i", gen(ts(i)))
        case ADT =>
          val (cty, ty) = cons(dty)(cx)
          gen(v); mg.getField(cty, s"a$i", gen(ty(i)))

    case Match(ty, rty, x, scrut, cs, other) =>
      val csmap = cs.toMap
      val (jty, kind, ccons) = tcons(ty)
      kind match
        case VoidLike =>
          val ty = Type.getType(classOf[Exception])
          mg.newInstance(ty)
          mg.dup()
          gen(scrut)
          mg.invokeVirtual(OBJECT_TYPE, Method.getMethod("String toString()"))
          mg.invokeConstructor(ty, Method.getMethod("void <init> (String)"))
          mg.throwException()
        case UnitLike => gen(scrut); mg.pop(); gen(cs(0)._2)
        case BoolLike =>
          val lFalse = new Label
          val lEnd = new Label
          gen(scrut)
          mg.visitJumpInsn(IFEQ, lFalse)
          gen(csmap(ccons(1)))
          mg.visitJumpInsn(GOTO, lEnd)
          mg.visitLabel(lFalse)
          gen(csmap(ccons(0)))
          mg.visitLabel(lEnd)
        case FiniteLike(k) =>
          if k <= 2 then impossible()
          gen(scrut)
          val labels = (0 until k).map(_ => mg.newLabel())
          mg.visitTableSwitchInsn(0, k - 1, labels.last, labels.toArray*)
          val lEnd = mg.newLabel()
          labels.zipWithIndex.foreach { (l, i) =>
            mg.visitLabel(l)
            gen(csmap(ccons(i)))
            mg.visitJumpInsn(GOTO, lEnd)
          }
          mg.visitLabel(lEnd)
        case NewtypeLike(t) =>
          val local = mg.newLocal(gen(t))
          gen(scrut)
          mg.storeLocal(local)
          gen(cs(0)._2)(mg, ctx, locals + (x -> (local, TCon(ty))), methodStart)
        case ProductLike(_) =>
          val local = mg.newLocal(jty)
          gen(scrut)
          mg.storeLocal(local)
          gen(cs(0)._2)(mg, ctx, locals + (x -> (local, TCon(ty))), methodStart)
        case _ =>
          gen(scrut)
          val lEnd = new Label
          var lNextCase = new Label
          val init = other match
            case None    => cs.init
            case Some(_) => cs
          init.foreach { (cx, b) =>
            val condata = cons(ty)(cx)
            val contype = condata._1
            val isNilary = condata._2.isEmpty
            mg.visitLabel(lNextCase)
            lNextCase = new Label
            mg.dup()
            if isNilary then
              mg.getStatic(jty, s"$$${escape(cx)}$$", contype)
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
              gen(b)(mg, ctx, locals + (x -> (local, TCon(ty))), methodStart)
            mg.visitJumpInsn(GOTO, lEnd)
          }
          mg.visitLabel(lNextCase)
          other match
            case None =>
              val (cx, last) = cs.last
              val condata = cons(ty)(cx)
              val contype = condata._1
              val isNilary = condata._2.isEmpty
              if isNilary then
                mg.pop()
                gen(last)
              else
                mg.checkCast(contype)
                val local = mg.newLocal(contype)
                mg.storeLocal(local)
                gen(last)(
                  mg,
                  ctx,
                  locals + (x -> (local, TCon(ty))),
                  methodStart
                )
            case Some(last) => mg.pop(); gen(last)
          mg.visitLabel(lEnd)
