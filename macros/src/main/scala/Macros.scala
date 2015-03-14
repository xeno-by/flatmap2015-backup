import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context

object fieldsOf {
  def apply(name: String): String = macro impl
  def impl(c: Context)(name: c.Tree): c.Tree = {
    import c.universe._
    import Flag._
    val q"${s_name: String}" = name
    val clazz = c.mirror.staticClass(s_name)
    val fields = clazz.toType.decls.filter(sym => sym.isTerm && sym.asTerm.isParamAccessor && sym.isPublic)
    q"${fields.map(_.name.toString).mkString(", ")}"
  }
}