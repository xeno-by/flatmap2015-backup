import scala.meta.XtensionQuasiquoteTerm
import scala.meta.dialects.Scala211
import scala.meta.internal.ast._
import scala.meta.tql._
import scala.obey.model._

object SetToList extends Rule {
  def description = "defining Set.toList is the same as defining a List"

  def message(t: Term): Message = Message(s"Set.toList is redundant in $t", t)

  def apply = transform {
    case t @ Term.Select(Term.Apply(Term.Name("Set"), l), Term.Name("toList")) =>
      Term.Apply(Term.Name("List"), l) andCollect message(t)
  }.topDown
}