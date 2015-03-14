import scala.collection.immutable.Set
import scala.collection.immutable.{ Set => MySet }
object Test extends App {
  val c = 3
  val v1 = Set(1, 2, 3).toList
  val v2 = MySet(1, 2, 3).toList
  var v3 = Set('a', 'b', 'c')
}