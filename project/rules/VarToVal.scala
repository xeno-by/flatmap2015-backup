import scala.meta.XtensionQuasiquoteTerm
import scala.meta.dialects.Scala211
import scala.meta.internal.ast._
import scala.meta.tql._
import scala.obey.model._
import scala.meta.semantic.Context

class VarToVal(implicit c: Context) extends Rule {
  def description = "defining an assigned-once var is the same as defining a val"

  def message(n: Tree, t: Tree): Message = Message(s"var is redundant in $t", t)

  def apply = {
    def collectAssignments = collect[Set] { case Term.Assign(b: Term.Name, _) => b }.topDown
    def transformVars(assignments: Set[Term.Name]) = transform {
      case t @ Defn.Var(a, Pat.Var.Term(b: Term.Name) :: Nil, c, Some(d)) if !assignments.contains(b) =>
        Defn.Val(a, Pat.Var.Term(b: Term.Name) :: Nil, c, d) andCollect message(b, t)
    }.topDown
    collectAssignments feed transformVars
  }
}