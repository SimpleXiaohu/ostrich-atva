package strsolver.preprop
import ap.parser._
import scala.collection.mutable.{ArrayBuffer, ArrayStack}

class LinearConstraints{
	// the stored formula
	var store : List[IFormula] = List()
	def addFormula(f : IFormula) = {
		store = f :: store
	}
	// return the stored formula
	def apply() = store
	override def toString = store.toString
}

object StoreLC{
	// the stored formula
	var store : IFormula = IBoolLit(true)
	def addFormula(f : IFormula) = {
		store = (f & store)
	}
 	// return the stored formula
	def apply() = store
}