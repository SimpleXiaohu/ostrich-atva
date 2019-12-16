package strsolver.preprop
import ap.terfor.ConstantTerm
// alloc constant term of register r. Id can not be greater than INTMAX
// e.g r = (R3, R4, R5)
object AllocRegisterTerm{
	var id = 0
	/**
	 * alloc register constant term
	 */
	def apply() = {
		val res = new ConstantTerm("R" + id)
		id += 1
		res
	 }
}

// alloc constant term of intermediate result t. 
// e.g t = (T3, T4, T5)
object AllocTTerm{
	var id = 0
	/**
	 * alloc t constant term
	 */
	def apply() = {
		val res = new ConstantTerm("T" + id)
		id += 1
		res
	 }
}

object AllocID{
	var id = 0

	def apply() = {
		id += 1
		id
	}
}

object GetTime{
	private var startTime : Long = _
	private def addTime : Unit = {
		startTime = System.nanoTime
	}
	override def toString : String = {
		val endTime : Long = System.nanoTime
		val timeMS = (endTime-startTime).toDouble / 1000000.0
		"time is "+timeMS+"\n"
	}
}