import scala.language.experimental.macros
import scala.meta._
import scala.meta.dialects.Scala211

package adt {
  trait Adt[T]
  object Adt {
    implicit def materialize[T]: Adt[T] = macro {
      T match {
        case ref: Type.Ref =>
          def validate(defn: Member): Unit = {
            def isEffectivelyFinal(defn: Member): Boolean = {
              if (defn.isFinal) true
              else if (defn.isSealed) defn.children.forall(x => x.isFinal)
              else false
            }
            if (!isEffectivelyFinal(defn)) abort(s"${defn.name} is not a final class/object or a sealed parent of final classes/objects")
            val cases = (defn +: defn.children).filter(x => x.isFinal)
            cases.filter(x => !x.isCase).foreach(x => abort(s"${x.name} is not a case class or a case object"))
            cases.filter(x => !x.tparams.isEmpty).foreach(x => abort(s"${x.name} is not monomorphic"))
          }
          validate(ref.defn)
          q"new _root_.adt.Adt[$T]{}"
        case _ =>
          abort(s"unsupported type $T")
      }
    }
  }
}

package serialization {
  trait Serializer[T] {
    def apply(x: T): String
  }

  object Serializer {
    implicit def materialize[T: adt.Adt]: Serializer[T] = macro {
      T match {
        case ref: Type.Ref =>
          def serializerFor(defn: Member, x: Term.Name, tagged: Boolean): Term = {
            if (defn.isFinal) {
              val serializedTag = {
                if (tagged) {
                  val tag = defn.parents.head.children.indexOf(defn).toString
                  q"""${"$tag"} + ": " + $tag"""
                } else {
                  q""" "" """
                }
              }
              val fields = defn.ctor.params.map(x => x.field)
              val serializedFields = fields.map(f => q"""${f.name.toString} + ": " + _root_.serialization.serialize($x.${f.name})""")
              val payload = serializedFields.foldLeft(serializedTag)((acc, curr) => q"""$acc + ", " + $curr""")
              q""" "{ " + $payload + " }" """
            } else {
              val cases = defn.children.map(child => {
                val x = Pat.fresh("x")
                p"case $x: ${child.tpe.pat} => ${serializerFor(child, x.name, tagged = true)}"
              })
              q"$x match { ..$cases }"
            }
          }
          val x = Term.fresh("x")
          val name = Term.fresh("Serializer")
          val body = serializerFor(ref.defn, x, tagged = false)
          q"""
            implicit object $name extends _root_.serialization.Serializer[$T] { 
              def apply($x: $T): _root_.scala.Predef.String = $body
            }
            $name
          """
        case _ =>
          abort(s"unsupported type $T")
      }
    }
    implicit def intSerializer: Serializer[Int] = new Serializer[Int] { def apply(x: Int) = x.toString }
    implicit def stringSerializer: Serializer[String] = new Serializer[String] { def apply(x: String) = x }
  }

  object serialize {
    def apply[T](x: T)(implicit ev: Serializer[T]) = ev(x)
  }
}

object Test extends App {
  import adt._
  import serialization._

  sealed trait List
  final case class Cons(head: Int, tail: List) extends List
  final case object Nil extends List

  val list: List = Cons(1, Cons(2, Nil))
  println(serialize(list))
}
