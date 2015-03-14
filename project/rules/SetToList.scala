import scala.meta.XtensionQuasiquoteTerm
import scala.meta.dialects.Scala211
import scala.meta.internal.ast._
import scala.meta.tql._
import scala.obey.model._
import scala.meta.semantic.Context

class SetToList(implicit c: Context) extends Rule {
  def description = "defining Set.toList is the same as defining a List"

  def message(t: Term): Message = Message(s"Set.toList is redundant in $t", t)

  def apply = transform {
    case t @ Term.Select(Term.Apply(set, l), Term.Name("toList"))
    if set == q"scala.collection.immutable.Set" =>
      Term.Apply(Term.Name("List"), l) andCollect message(t)
  }.topDown
}