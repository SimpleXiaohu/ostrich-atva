package strsolver


import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.preds.Predicate

//store the input int constraints 
object IntConstraintStore{
  var formula : Formula = _
  def apply() = formula
  def setFormula(f : Formula) : Unit = {
    formula = f
  }
}
