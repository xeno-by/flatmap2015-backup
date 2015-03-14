import scala.language.experimental.macros
import scala.meta._
import scala.meta.dialects.Scala211

package adt {
  trait Adt[T]
  object Adt {
    implicit def materialize[T]: Adt[T] = macro {
      ???
    }
  }
}

package serialization {
  trait Serializer[T] {
    def apply(x: T): String
  }

  object Serializer {
    implicit def materialize[T: adt.Adt]: Serializer[T] = macro {
      ???
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
