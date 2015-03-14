import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context

object fieldsOf {
  def apply[T]: String = macro impl[T]
  def impl[T](c: Context)(implicit T: c.WeakTypeTag[T]): c.Expr[String] = {
    import c.universe._
    import Flag._
    val fields = T.tpe.decls.filter(sym => sym.isTerm && sym.asTerm.isParamAccessor && sym.isPublic)
    c.Expr[String](q"${fields.map(_.name.toString).mkString(", ")}")
  }
}