package strsolver.preprop
import ap.basetypes.IdealInt
import ap.parser.Internal2InputAbsy
import ap.terfor.Term
import ap.terfor.linearcombination.LinearCombination

import scala.collection.mutable.SortedSet

object SubStringPreOp{
  def apply(i : Term, j : Term) : PreOp = {
    new SubStringPreOp(i,j)
  }
}

class SubStringPreOp(i : Term, j : Term) extends PreOp{
  // TODO : add logic
	def apply(argumentConstraints : Seq[Seq[Automaton]],
            resultConstraint : Automaton)
          : (Iterator[(Seq[Automaton], LinearConstraints)], Seq[Seq[Automaton]]) = {
    val input_i = Internal2InputAbsy(i)
    val input_j = Internal2InputAbsy(j)

    val a = new LinearConstraints
    val resAut = AtomicStateAutomatonAdapter.intern(resultConstraint).asInstanceOf[BricsAutomaton]
    val builder = resAut.getBuilder
    val initState = builder.getNewState
    val infiniteCycleS = builder.getNewState
    builder.setInitialState(initState)
    builder.setAccept(infiniteCycleS, true)
    val resAutRLen = resAut.registers.size    // resAut registers size
    val tmpList = List.fill(resAutRLen)(0)
    val sigma = builder.LabelOps.sigmaLabel

    val resAutSLen = resAut.states.size       // resAut registers size
    val states1 = List.fill(resAutSLen)(builder.getNewState)
    // from resAut states map to new states
    val sMap = (resAut.states zip states1).toMap

    var needIFCS : Boolean = false
    for((ts, (charMin, charMax)) <- resAut.outgoingTransitions(resAut.initialState)){
      val vector = resAut.etaMap((resAut.initialState, (charMin,charMax), ts))
      builder.addTransition(initState, (charMin,charMax), sMap(ts), List(0,0)++vector)
    }

    builder.addTransition(initState, sigma, initState, List(1,1)++tmpList)

    for(fs <- resAut.states){
      val fsIsAccept = resAut.acceptingStates(fs)
      builder.setAccept(sMap(fs), fsIsAccept)
      for((ts, label) <- resAut.outgoingTransitions(fs)){
        val vector = resAut.etaMap((fs, label, ts))
        builder.addTransition(sMap(fs), label, sMap(ts), List(0,1)++vector)
      }
      if(fsIsAccept)
        if(builder.etaMap.contains(((sMap(fs), sigma, sMap(fs))))){
          needIFCS = true
          builder.addTransition(sMap(fs),sigma,infiniteCycleS, List(0,0)++tmpList)
        }else
          builder.addTransition(sMap(fs), sigma, sMap(fs), List(0,0)++tmpList)
    }
    if(needIFCS)
      builder.addTransition(infiniteCycleS,sigma,infiniteCycleS, List(0,0)++tmpList)
    val res = builder.getAutomaton
    res.addEtaMaps(builder.etaMap)
    res.addNewRegister(2)   // i,j
    res.addRegisters(resAut.registers)  // New registers is (i, j)++resAut.registers
    a.addFormula(res.registers(0) === input_i)
    a.addFormula(res.registers(1) === input_j)

    (Iterator((Seq(res), a)), List())
  }
    
  def eval(arguments : Seq[Seq[Int]]) : Option[Seq[Int]] = {

    	val strLen = arguments(0).size
      val i_option = IdealInt.unapply(i.asInstanceOf[LinearCombination].constant)
      val j_option = IdealInt.unapply(j.asInstanceOf[LinearCombination].constant)
      if (i_option == None || j_option == None)
        return None
      val i_value = i_option.get
      val j_value = j_option.get
      if(i_value < 0 || j_value > strLen-1)
        return None

      return Some(arguments(0).slice(i_value, j_value+1))

    }
 	override def toString = "substring{"+i.toString+","+j.toString+"}"

}