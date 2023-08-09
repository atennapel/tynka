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

  private type Locals = IntMap[Either[Tm, (Int, Ty)]]

  private final case class Ctx(moduleName: String, moduleType: Type)
  private val tcons: mutable.Map[GName, (Type, DataKind, List[GName])] =
    mutable.Map.empty
  private val cons: mutable.Map[GName, mutable.Map[GName, (Type, List[Ty])]] =
    mutable.Map.empty

  private def conIsFirst(dx: GName, cx: GName): Boolean =
    tcons(dx)._3.head == cx

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

    // generate main
    val mainexists = ds.defs.exists {
      case DDef("main", false, TDef(Some(Nil), _), _) => true
      case _                                          => false
    }
    if mainexists then
      val m = new Method(
        "main",
        Type.VOID_TYPE,
        List(Type.getType("[Ljava/lang/String;")).toArray
      )
      val main: GeneratorAdapter =
        new GeneratorAdapter(ACC_PUBLIC + ACC_STATIC, m, null, null, cw)
      main.invokeStatic(
        ctx.moduleType,
        new Method("main", Type.BOOLEAN_TYPE, List().toArray)
      )
      main.pop()
      main.visitInsn(RETURN)
      main.visitMaxs(3, 1)
      main.visitEnd

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
    case TArray(ty)    => Type.getType(s"[${gen(ty).getDescriptor()}")
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
    case TConCon(x, c) =>
      val (t, k, _) = tcons(x)
      k match
        case UnitLike       => Type.BOOLEAN_TYPE
        case BoolLike       => Type.BOOLEAN_TYPE
        case VoidLike       => Type.BOOLEAN_TYPE
        case FiniteLike(_)  => Type.INT_TYPE
        case NewtypeLike(t) => gen(t)
        case _ => Type.getType(s"${t.getDescriptor().init}$$${escape(c)};")

  private def constantValue(e: Tm): Option[Any] = e match
    case IntLit(n)          => Some(n)
    case BoolLit(n)         => Some(n)
    case StringLit(n)       => Some(n)
    case Con(_, _, List(v)) => constantValue(v)
    case _                  => None

  private val primitives = "BCDFIJSZ".split("")
  private def descriptorIsPrimitive(d: String): Boolean = primitives.contains(d)

  private def isBoxed(t: Ty): Boolean = t match
    case TArray(_)                               => true
    case TForeign(d) if descriptorIsPrimitive(d) => false
    case TForeign(_)                             => true
    case TConCon(x, _)                           => isBoxed(TCon(x))
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
          s"$$$ecx$$",
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
        ACC_PUBLIC,
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
        ACC_PUBLIC,
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
    case BoolLit(v)   => mg.push(v)
    case StringLit(v) => mg.push(v)
    case Arg(ix)      => mg.loadArg(ix)
    case Var(x) =>
      locals(x) match
        case Left(t)       => gen(t)
        case Right((l, _)) => mg.loadLocal(l)

    case Global(x, t) => mg.getStatic(ctx.moduleType, name(x), gen(t))
    case GlobalApp(x, TDef(Some(ps), rt), true, as) if name(x) == mg.getName =>
      as.foreach(gen)
      Range.inclusive(as.size - 1, 0, -1).foreach(i => mg.storeArg(i))
      // local clearing to allow gc (taken from Clojure)
      locals.values.foreach {
        case Right((l, ty)) =>
          if isBoxed(ty) then
            mg.visitInsn(Opcodes.ACONST_NULL)
            mg.storeLocal(l)
        case _ =>
      }
      mg.visitJumpInsn(GOTO, methodStart)
    case GlobalApp(x, TDef(Some(ps), rt), _, as) =>
      as.foreach(gen)
      mg.invokeStatic(
        ctx.moduleType,
        new Method(name(x), gen(rt), ps.map(gen).toArray)
      )
    case GlobalApp(_, _, _, _) => impossible()

    case Let(x, t, InvokeVirtualVoid(arg, as), b) =>
      invokeVirtualVoid(arg, as); gen(b)
    case Let(x, t, v, b) =>
      val entry = genLocal(v, gen(t), t)
      gen(b)(mg, ctx, locals + (x -> entry), methodStart)

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
          val conType =
            Type.getType(s"L${ctx.moduleName}$$$ty$$${escape(con)};")
          mg.getStatic(
            tcons(ty)._1,
            s"$$${escape(con)}$$",
            conType
          )
        case _ =>
          val conType =
            Type.getType(s"L${ctx.moduleName}$$$ty$$${escape(con)};")
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
        case UnitLike =>
          scrut match
            case InvokeVirtualVoid(arg, as) =>
              invokeVirtualVoid(arg, as); gen(cs(0)._2)
            case _ => gen(scrut); mg.pop(); gen(cs(0)._2)
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
          val entry = genLocal(scrut, gen(t), t)
          gen(cs(0)._2)(
            mg,
            ctx,
            locals + (x -> entry),
            methodStart
          )
        case ProductLike(_) =>
          val entry = genLocal(scrut, jty, TCon(ty))
          gen(cs(0)._2)(mg, ctx, locals + (x -> entry), methodStart)
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
              gen(b)(
                mg,
                ctx,
                locals + (x -> Right((local, TCon(ty)))),
                methodStart
              )
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
                  locals + (x -> Right((local, TCon(ty)))),
                  methodStart
                )
            case Some(last) => mg.pop(); gen(last)
          mg.visitLabel(lEnd)

    case Foreign(_, "cast", List((v, _)))       => gen(v)
    case Foreign(_, "returnVoid", List((v, _))) => gen(v); mg.pop()
    case Foreign(_, op, List((p, _), (c, _))) if op.startsWith("catch") =>
      val exc = op match
        case "catch"                     => null
        case s if s.startsWith("catch:") => s.drop(6)
        case _                           => impossible()
      val lStart = mg.newLabel()
      val lStop = mg.newLabel()
      val lHandler = mg.newLabel()
      val lEnd = mg.newLabel()
      mg.visitTryCatchBlock(lStart, lStop, lHandler, exc)
      mg.visitLabel(lStart)
      gen(p)
      mg.visitLabel(lStop)
      mg.visitJumpInsn(GOTO, lEnd)
      mg.visitLabel(lHandler)
      mg.pop()
      gen(c)
      mg.visitLabel(lEnd)
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
    case Foreign(
          rt @ TArray(ty),
          "arrayUnsafeNew",
          List((length, _))
        ) =>
      val ety = gen(ty)
      gen(length)
      mg.newArray(ety)
    case Foreign(
          rt @ TArray(ty),
          "arrayNew",
          List((length, _), (initial, _))
        ) =>
      val ety = gen(ty)
      gen(length)
      (ety.getDescriptor(), initial) match
        case (d, IntLit(0)) if descriptorIsPrimitive(d) => mg.newArray(ety)
        case (d, Con(dx, cx, Nil))
            if descriptorIsPrimitive(d) && conIsFirst(dx, cx) =>
          mg.newArray(ety)
        case _ =>
          val lengthLocal = mg.newLocal(Type.INT_TYPE)
          mg.storeLocal(lengthLocal)
          mg.loadLocal(lengthLocal)
          mg.newArray(ety)
          gen(initial)
          mg.push(0)
          val indexLocal = mg.newLocal(Type.INT_TYPE)
          mg.storeLocal(indexLocal)
          val start = mg.newLabel()
          val end = mg.newLabel()
          /*
          array
          value
           */
          mg.visitLabel(start)
          // jump to end if index >= length
          mg.loadLocal(indexLocal)
          mg.loadLocal(lengthLocal)
          mg.ifICmp(IFGE, end)
          // set value in array
          mg.dup2()
          mg.loadLocal(indexLocal)
          mg.swap()
          mg.arrayStore(ety)
          // inc index
          mg.iinc(indexLocal, 1)
          mg.visitJumpInsn(GOTO, start)
          mg.visitLabel(end)
          mg.pop()
    case Foreign(
          ty,
          "arrayGet",
          List((index, _), (array, _))
        ) =>
      val ety = gen(ty)
      gen(array)
      gen(index)
      mg.arrayLoad(ety)
    case Foreign(
          _,
          "arraySet",
          List((index, _), (value, _), (array, TArray(ty)))
        ) =>
      val ety = gen(ty)
      gen(array)
      gen(index)
      gen(value)
      mg.arrayStore(ety)
      mg.push(false)
    case Foreign(
          _,
          "arrayLength",
          List((array, _))
        ) =>
      gen(array)
      mg.arrayLength()
    case Foreign(rt, cmd0, as) =>
      val (cmd, arg) = splitForeign(cmd0)
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
          invokeVirtualVoid(arg, as); mg.push(false)
        case ("invokeStatic", arg, as) =>
          val ss = arg.split("\\.")
          val owner = s"L${ss.init.mkString("/")};"
          val member = ss.last
          as.foreach((v, _) => gen(v))
          mg.invokeStatic(
            Type.getType(owner),
            Method(member, gen(rt), as.map((_, t) => gen(t)).toArray)
          )
        case ("mutateData", str, List((d, td), (v, tv))) =>
          val spl = str.reverse.split("\\:")
          val i = spl.head.reverse
          if spl.size == 1 then
            gen(d)
            mg.dup()
            gen(v)
            mg.putField(gen(td), s"a$i", gen(tv))
          else
            val con = escape(spl.tail.mkString(":").reverse)
            val x = td match
              case TCon(x)       => x
              case TConCon(x, _) => x
              case TForeign(cls) => impossible()
              case TArray(ty)    => impossible()
            val tc = cons(x)(con)._1
            gen(d)
            mg.checkCast(tc)
            mg.dup()
            gen(v)
            mg.putField(tc, s"a$i", gen(tv))
        case ("mutateDataUnit", str, List((d, td), (v, tv))) =>
          val spl = str.reverse.split("\\:")
          val i = spl.head.reverse
          if spl.size == 1 then
            gen(d)
            gen(v)
            mg.putField(gen(td), s"a$i", gen(tv))
            mg.push(false)
          else
            val con = escape(spl.tail.mkString(":").reverse)
            val x = td match
              case TCon(x)       => x
              case TConCon(x, _) => x
              case TForeign(cls) => impossible()
              case TArray(ty)    => impossible()
            val tc = cons(x)(con)._1
            gen(d)
            mg.checkCast(tc)
            gen(v)
            mg.putField(tc, s"a$i", gen(tv))
            mg.push(false)
        case ("mutateCon", str, List((d, td), (v, tv))) =>
          val spl = str.reverse.split("\\:")
          val i = spl.head.reverse
          if spl.size == 1 then
            gen(d)
            mg.dup()
            gen(v)
            mg.putField(gen(td), s"a$i", gen(tv))
          else
            val con = escape(spl.tail.mkString(":").reverse)
            val x = td match
              case TConCon(x, _) => x
              case TCon(x)       => impossible()
              case TForeign(cls) => impossible()
              case TArray(ty)    => impossible()
            val tc = cons(x)(con)._1
            gen(d)
            mg.dup()
            gen(v)
            mg.putField(tc, s"a$i", gen(tv))
        case ("mutateConUnit", str, List((d, td), (v, tv))) =>
          val spl = str.reverse.split("\\:")
          val i = spl.head.reverse
          if spl.size == 1 then
            gen(d)
            gen(v)
            mg.putField(gen(td), s"a$i", gen(tv))
            mg.push(false)
          else
            val con = escape(spl.tail.mkString(":").reverse)
            val x = td match
              case TConCon(x, _) => x
              case TCon(x)       => impossible()
              case TForeign(cls) => impossible()
              case TArray(ty)    => impossible()
            val tc = cons(x)(con)._1
            gen(d)
            gen(v)
            mg.putField(tc, s"a$i", gen(tv))
            mg.push(false)
        case _ => impossible()

  private def genLocal(scrut: Tm, jty: Type, t: Ty)(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      locals: Locals,
      methodStart: Label
  ): Either[Tm, (Int, Ty)] =
    scrut match
      case Arg(ix) => Left(scrut)
      case Var(ix) => Left(scrut)
      case _ =>
        val local = mg.newLocal(jty)
        gen(scrut)
        mg.storeLocal(local)
        Right((local, t))

  private def splitForeign(cmd0: String): (String, String) =
    val s = cmd0.split("\\:")
    val cmd = s.head
    val arg = s.tail.mkString(":")
    (cmd, arg)
  private def invokeVirtualVoid(arg: String, as: List[(Tm, Ty)])(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      locals: Locals,
      methodStart: Label
  ): Unit =
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

  private object InvokeVirtualVoid:
    def unapply(t: Tm): Option[(String, List[(Tm, Ty)])] = t match
      case Foreign(_, cmd0, as) =>
        val (cmd, arg) = splitForeign(cmd0)
        if cmd == "invokeVirtualVoid" then Some((arg, as))
        else None
      case _ => None
