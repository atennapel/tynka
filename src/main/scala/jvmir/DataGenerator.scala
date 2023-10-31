package jvmir

import common.Common.*
import Syntax.*
import JvmName.escape

import org.objectweb.asm.*
import org.objectweb.asm.commons.*
import org.objectweb.asm.Opcodes.*

import scala.collection.mutable
import java.io.BufferedOutputStream
import java.io.FileOutputStream

object DataGenerator:
  private final case class DataInfo(
      jname: String,
      desc: String,
      ty: Type,
      cons: List[Name]
  )
  private val types: mutable.Map[Name, DataInfo] = mutable.Map.empty
  private final case class ConInfo(
      jname: String,
      data: Name,
      className: String,
      desc: String,
      ty: Type,
      params: List[(String, Type)]
  )
  private val cons: mutable.Map[Name, ConInfo] = mutable.Map.empty

  def genDatatypes(ds: List[Def]): Unit =
    ds.foreach {
      case DData(dx, cs) =>
        val edx = escape(dx.expose)
        val desc = s"L$edx;"
        types += (dx -> DataInfo(
          edx,
          desc,
          Type.getType(desc),
          cs.map((cx, _) => cx)
        ))
        cs.foreach { (cx, params) =>
          val ecx = escape(cx.expose)
          val className = s"$edx$$$ecx"
          val desc = s"L$className;"
          val eparams = params.zipWithIndex.map { case ((x, t), i) =>
            val y = x match
              case DoBind(x) => escape(x.expose)
              case DontBind  => s"a$i"
            (y, gen(t))
          }
          cons += (cx -> ConInfo(
            ecx,
            dx,
            className,
            desc,
            Type.getType(desc),
            eparams
          ))
        }
      case _ =>
    }
    ds.foreach {
      case DData(dx, cs) => genData(dx, cs)
      case _             =>
    }

  def gen(t: Ty): Type = t match
    case TCon(dx) => types(dx).ty

  private def genData(dx: Name, cs: List[(Name, List[(Bind, Ty)])]): Unit =
    val className = types(dx).jname
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
    cs.foreach { case (cx, as) =>
      val ecx = cons(cx).jname
      val conClassName = cons(cx).className
      val conDesc = cons(cx).desc
      genCon(cx)
      datacw.visitInnerClass(
        conClassName,
        className,
        s"$$$ecx",
        ACC_PUBLIC + ACC_STATIC + ACC_FINAL
      )
      if as.isEmpty then
        datacw.visitField(
          ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
          s"$$$ecx$$",
          conDesc,
          null,
          null
        )
    }

    // 0-ary constructor initialization
    val m = new Method("<clinit>", Type.VOID_TYPE, Nil.toArray)
    implicit val stmg: GeneratorAdapter =
      new GeneratorAdapter(ACC_STATIC, m, null, null, datacw)
    cs.foreach { case (cx, as) =>
      val ecx = cons(cx).jname
      if as.isEmpty then
        val conType = cons(cx).ty
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
        stmg.putStatic(Type.getType(cons(cx).desc), s"$$$ecx$$", conType)
    }
    stmg.visitInsn(RETURN)
    stmg.endMethod()

    // output
    datacw.visitEnd()
    /*
    cw.visitInnerClass(
      className,
      ???,
      className,
      ACC_PUBLIC + ACC_ABSTRACT + ACC_STATIC
    )*/
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$className.class")
    )
    bos.write(datacw.toByteArray())
    bos.close()

  private def genCon(cx: Name): Unit =
    val info = cons(cx)
    val className = info.className
    val superName = types(info.data).jname
    val params = info.params
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
    params.zipWithIndex.foreach { case ((x, ty), i) =>
      cw.visitField(ACC_PUBLIC + ACC_FINAL, x, ty.getDescriptor, null, null)
    }

    // class constructor
    val m = new Method("<init>", Type.VOID_TYPE, params.map(_._2).toArray)
    val mg: GeneratorAdapter =
      new GeneratorAdapter(
        if params.isEmpty then ACC_PROTECTED else ACC_PUBLIC,
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
    params.zipWithIndex.foreach { case ((x, ty), i) =>
      mg.loadThis()
      mg.loadArg(i)
      mg.putField(info.ty, x, ty)
    }
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
