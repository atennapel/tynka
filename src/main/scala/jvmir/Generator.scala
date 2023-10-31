package jvmir

import common.Common.*
import common.Debug.debug
import Syntax.*
import JvmName.*
import DataGenerator.*

import org.objectweb.asm.*
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.commons.*

import scala.collection.mutable
import scala.collection.immutable.IntMap
import scala.annotation.tailrec

import java.io.BufferedOutputStream
import java.io.FileOutputStream

object Generator:
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

  private val primitives = "BCDFIJSZ".split("")
  private def descriptorIsPrimitive(d: String): Boolean = primitives.contains(d)

  private enum LocalEntry:
    case LLocal(local: Int, ty: Ty)
    case LTm(tm: Tm)
    case LJoin(label: Label, params: List[Int])
  import LocalEntry.*
  private type Locals = IntMap[LocalEntry]
  private final case class Ctx(moduleName: String, moduleType: Type)

  def generate(module0: String, ds: List[Def]): Unit =
    val module = escape(module0)
    implicit val ctx: Ctx = Ctx(module, Type.getType(s"L$module;"))
    implicit val cw: ClassWriter = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    ) {
      override protected def getCommonSuperClass(
          type1: String,
          type2: String
      ): String =
        val prefix = longestCommonPrefix(type1, type2)
        val ret = if prefix.endsWith("$") then prefix.init else prefix
        // debug(s"getCommonSuperClass $type1 $type2 $prefix $ret")
        ret
    }
    cw.visit(
      V1_8,
      ACC_PUBLIC + ACC_FINAL,
      escape(module),
      null,
      "java/lang/Object",
      null
    )

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
    genDatatypes(ds, Some((cw, module)))
    ds.foreach(gen)

    // generate main
    val mainexists = ds.exists {
      case DDef(
            false,
            Name("main"),
            TDef(Some(List(_)), _),
            _
          ) =>
        true
      case _ => false
    }
    if mainexists then
      val m = new Method(
        "main",
        Type.VOID_TYPE,
        List(Type.getType("[Ljava/lang/String;")).toArray
      )
      val main: GeneratorAdapter =
        new GeneratorAdapter(ACC_PUBLIC + ACC_STATIC, m, null, null, cw)
      main.visitInsn(ACONST_NULL)
      main.invokeStatic(
        ctx.moduleType,
        new Method(
          escape("main"),
          OBJECT_TYPE,
          List(OBJECT_TYPE).toArray
        )
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
      new FileOutputStream(s"$module.class")
    )
    bos.write(cw.toByteArray())
    bos.close()

  private def constantValue(e: Tm): Option[Any] = e match
    case _ => None

  private def genStaticBlock(
      ds0: List[Def]
  )(implicit cw: ClassWriter, ctx: Ctx): Unit =
    val ds = ds0.toList.filter {
      case DDef(_, x, TDef(None, _), b) if constantValue(b).isEmpty =>
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
          case DDef(_, x, TDef(None, rt), b) =>
            gen(b)
            mg.putStatic(ctx.moduleType, escape(x.expose), genTy(rt))
          case _ =>
      })
      mg.visitInsn(RETURN)
      mg.endMethod()

  private def gen(d: Def)(implicit cw: ClassWriter, ctx: Ctx): Unit = d match
    case DData(_, _) =>
    case DDef(g, x, TDef(None, rt), v) =>
      cw.visitField(
        (if g then ACC_PRIVATE + ACC_SYNTHETIC
         else ACC_PUBLIC) + ACC_FINAL + ACC_STATIC,
        escape(x.expose),
        genTy(rt).getDescriptor,
        null,
        constantValue(v).orNull
      )
    case DDef(g, x, TDef(Some(ts), rt), v) =>
      val m = new Method(
        escape(x.expose),
        genTy(rt),
        ts.map(genTy).toArray
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
      gen(v)
      mg.returnValue()
      mg.endMethod()

  private def gen(
      t: Tm
  )(implicit mg: GeneratorAdapter, ctx: Ctx, locals: Locals): Unit =
    t match
      case Arg(ix) => mg.loadArg(ix)
      case Var(x) =>
        locals(x) match
          case LTm(t)       => gen(t)
          case LLocal(l, _) => mg.loadLocal(l)
          case _            => impossible()
      case Global(x, ty) =>
        mg.getStatic(ctx.moduleType, escape(x.expose), genTy(ty))
      case GlobalApp(x, TDef(Some(ps), rt), as) =>
        as.foreach(gen)
        mg.invokeStatic(
          ctx.moduleType,
          new Method(escape(x.expose), genTy(rt), ps.map(genTy).toArray)
        )
      case GlobalApp(_, _, _) => impossible()

      case Let(x, ty, v, b) =>
        val entry = genLocal(v, genTy(ty), ty)
        gen(b)(mg, ctx, locals + (x -> entry))

      case Join(x, ps, v, b) =>
        val lps = ps.map { (x, t) =>
          (x, t, mg.newLocal(genTy(t)))
        }
        val lJoin = mg.newLabel()
        val lEnd = mg.newLabel()
        gen(b)(mg, ctx, locals + (x -> LJoin(lJoin, lps.map(_._3))))
        mg.visitJumpInsn(GOTO, lEnd)
        mg.visitLabel(lJoin)
        gen(v)(mg, ctx, locals ++ lps.map((x, t, l) => (x, LLocal(l, t))))
        mg.visitLabel(lEnd)
      case JoinRec(x, ps, v, b) =>
        val lps = ps.map { (x, t) =>
          (x, t, mg.newLocal(genTy(t)))
        }
        val lJoin = mg.newLabel()
        val lEnd = mg.newLabel()
        val joinEntry = x -> LJoin(lJoin, lps.map(_._3))
        gen(b)(mg, ctx, locals + joinEntry)
        mg.visitJumpInsn(GOTO, lEnd)
        mg.visitLabel(lJoin)
        gen(v)(
          mg,
          ctx,
          locals + joinEntry ++ lps.map((x, t, l) => (x, LLocal(l, t)))
        )
        mg.visitLabel(lEnd)
      case Jump(x, args) =>
        locals(x) match
          case LJoin(lbl, params) =>
            args.foreach(gen)
            params.reverse.foreach(l => mg.storeLocal(l))
            mg.visitJumpInsn(GOTO, lbl)
          case _ => impossible()

      case Con(cx, as) =>
        val info = conInfo(cx)
        as match
          case Nil =>
            mg.getStatic(
              dataInfoFromCon(cx).ty,
              s"$$${info.jname}$$",
              info.ty
            )
          case as =>
            mg.newInstance(info.ty)
            mg.dup()
            as.foreach(gen)
            mg.invokeConstructor(
              info.ty,
              new Method(
                "<init>",
                Type.VOID_TYPE,
                info.params.map(_._2).toArray
              )
            )
      case Field(cx, v, ix) =>
        val info = conInfo(cx)
        val (x, ty) = info.params(ix)
        gen(v)
        mg.getField(info.ty, x, ty)
      case Match(s, cx, x, b, o) =>
        val info = conInfo(cx)
        val dataInfo = dataInfoFromCon(cx)
        val nilary = info.params.isEmpty
        gen(s)
        o match
          case Some(o) =>
            val lEnd = new Label
            var lOther = new Label
            mg.dup()
            if nilary then
              mg.getStatic(dataInfo.ty, s"$$${info.jname}$$", info.ty)
              mg.visitJumpInsn(IF_ACMPNE, lOther)
              mg.pop()
              gen(b)
            else
              mg.instanceOf(info.ty)
              mg.visitJumpInsn(IFEQ, lOther)
              mg.checkCast(info.ty)
              val local = mg.newLocal(info.ty)
              mg.storeLocal(local)
              gen(b)(
                mg,
                ctx,
                locals + (x -> LLocal(local, TCon(info.data)))
              )
            mg.visitJumpInsn(GOTO, lEnd)
            mg.visitLabel(lOther)
            mg.pop()
            gen(o)
            mg.visitLabel(lEnd)
          case None =>
            if nilary then
              mg.pop()
              gen(b)
            else
              mg.checkCast(info.ty)
              val local = mg.newLocal(info.ty)
              mg.storeLocal(local)
              gen(b)(
                mg,
                ctx,
                locals + (x -> LLocal(local, TCon(info.data)))
              )

  private def genLocal(scrut: Tm, jty: Type, t: Ty)(implicit
      mg: GeneratorAdapter,
      ctx: Ctx,
      locals: Locals
  ): LocalEntry =
    scrut match
      case Arg(ix) => LTm(scrut)
      case Var(ix) => LTm(scrut)
      case _ =>
        val local = mg.newLocal(jty)
        gen(scrut)
        mg.storeLocal(local)
        LLocal(local, t)
