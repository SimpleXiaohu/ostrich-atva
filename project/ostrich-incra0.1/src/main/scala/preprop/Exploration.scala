/*
 * This file is part of Sloth, an SMT solver for strings.
 * Copyright (C) 2018  Matthew Hague, Philipp Ruemmer
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package strsolver.preprop

import strsolver.{IntConstraintStore}
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.basetypes.IdealInt
import ap.parser.{IExpression, Internal2InputAbsy, SMTLineariser, SymbolCollector}
import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.substitutions.VariableSubst
import ap.theories.TheoryRegistry
import ap.util.Seqs

import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}

case class TermConstraint(t : Term, aut : Automaton)
object Exploration {

  type ConflictSet = Seq[TermConstraint]

  abstract class ConstraintStore {
    def push : Unit

    def pop : Unit

    /**
     * Add new automata to the store, return a sequence of term constraints
     * in case the asserted constraints have become inconsistent
     */
    def assertConstraint(aut : Automaton) : Option[ConflictSet]

    /**
     * Return some representation of the asserted constraints
     */
    def getContents : List[Automaton]

    /**
     * Return all constraints that were asserted (without any modifications)
     */
    def getCompleteContents : List[Automaton]

    /**
     * Make sure that the exact length abstraction for the intersection of the
     * stored automata has been pushed to the length prover
     */
//    def ensureCompleteLengthConstraints : Unit

    /**
     * Produce an arbitrary word accepted by all the stored constraints
     */
    def getAcceptedWord : Seq[Int]

    /**
     * Produce a word of length <code>len</code> accepted by all the stored
     * constraints
     */
    def getAcceptedWordLen(len : Int) : Seq[Int]
  }

  def lazyExp(funApps : Seq[(PreOp, Seq[Term], Term)],
              // huzi add 
              intFunApps : Seq[(PreOp, Seq[Term], Term)],
              // huzi add
              initialConstraints : Seq[(Term, Automaton)],
              // lengthProver : Option[SimpleAPI],
              lengthVars : Map[Term, Term],
              strictLengths : Boolean) : Exploration =
    new LazyExploration(funApps, intFunApps, initialConstraints,
                        lengthVars, strictLengths)

  private case class FoundModel(model : Map[Term, Seq[Int]]) extends Exception


  def measure[A](op : String)(comp : => A) : A =
//    if (Flags.measureTimes)
//      ap.util.Timer.measure(op)(comp)
//    else
      comp
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Depth-first exploration of a conjunction of function applications
 */
abstract class Exploration(val funApps : Seq[(PreOp, Seq[Term], Term)],
                           // huzi add 
                           val intFunApps : Seq[(PreOp, Seq[Term], Term)],
                           // huzi add 
                           val initialConstraints : Seq[(Term, Automaton)],
                           // lengthProver : Option[SimpleAPI],
                           lengthVars : Map[Term, Term],
                           strictLengths : Boolean) {

  import Exploration._
//debug----------------
  println
  println("Running preprop solver")

  val notAtomTermSet = new MHashSet[Term]()
  // store int constraints deriving from preimage
  val LCStack = new ArrayStack[LinearConstraints]

  private val (allTerms, sortedFunApps)
              : (Set[Term], Seq[(Seq[(PreOp, Seq[Term])], Term)]) = {
    val argTermNum = new MHashMap[Term, Int]    
    for ((_, _, res) <- funApps) {
      argTermNum.put(res, 0)
      notAtomTermSet += res
    }
    for ((t, _) <- initialConstraints)
      argTermNum.put(t, 0)    
    for ((_, args, _) <- funApps; a <- args)
      argTermNum.put(a, argTermNum.getOrElse(a, 0) + 1)  


    var remFunApps = funApps
    val sortedApps = new ArrayBuffer[(Seq[(PreOp, Seq[Term])], Term)]

    while (!remFunApps.isEmpty) {
      val (selectedApps, otherApps) =
        remFunApps partition { case (_, _, res) => argTermNum(res) == 0 }
      remFunApps = otherApps

      for ((_, args, _) <- selectedApps; a <- args)
        argTermNum.put(a, argTermNum.getOrElse(a, 0) - 1)

      assert(!selectedApps.isEmpty)

      val appsPerRes = selectedApps groupBy (_._3)
      // non-repeat non-arg(in other words, res) Terms
      val nonArgTerms = (selectedApps map (_._3)).distinct

      for (t <- nonArgTerms)
        sortedApps +=
          ((for ((op, args, _) <- appsPerRes(t)) yield (op, args), t))
    }

    // huzi add
    val intApps = new ArrayBuffer[(Seq[(PreOp, Seq[Term])], Term)]

    for ((op, args, t) <- intFunApps; a <- args){
      argTermNum.put(a, argTermNum.getOrElse(a, 0) + 1)
    }
    for ((op, args, t) <- intFunApps){
      argTermNum.put(t,0)
      intApps += ((Seq((op,args)), t))
    }


    val allFunApps : Seq[(Seq[(PreOp, Seq[Term])], Term)]
      = intApps ++ sortedApps

    (argTermNum.keySet.toSet, allFunApps)
    

  }

  for ((ops, t) <- sortedFunApps)
    if (ops.size > 1) {
      printf("Mutiple definitions found for "+t+"\n")
      printf("unknow\n")
      System.exit(1)
    }

//debug----------------
  println("   Considered function applications:")
  for ((apps, res) <- sortedFunApps) {
    println("   " + res + " =")
    for ((op, args) <- apps)
      println("     " + op + "(" + (args mkString ", ") + ")")
  }



  //////////////////////////////////////////////////////////////////////////////

  // check whether we have to add further regex constraints to ensure
  // completeness; otherwise not all pre-images of function applications might
  // be considered
  
  val allInitialConstraints = {
    val term2Index =
      (for (((_, t), n) <- sortedFunApps.iterator.zipWithIndex)
       yield (t -> n)).toMap

    val coveredTerms = new MBitSet
    for ((t, _) <- initialConstraints)
      for (ind <- term2Index get t)
        coveredTerms += ind

    val additionalConstraints = new ArrayBuffer[(Term, BricsAutomaton)]

    for (n <- 0 until sortedFunApps.size;
         if {
           if (!(coveredTerms contains n)) {
             coveredTerms += n
             additionalConstraints +=
               ((sortedFunApps(n)._2, BricsAutomaton.makeAnyString()))
           }
           true
         };
         (_, args) <- sortedFunApps(n)._1;
         arg <- args)
      for (ind <- term2Index get arg)
        coveredTerms += ind

    initialConstraints ++ additionalConstraints
  }

  ///////////////////////////////////////////////////////////////////////////////
  // get product of all initial automata
  val autSet = allInitialConstraints.groupBy(_._1).map(_._2)
    .map(_.map(_._2))
    .map(_.map(_.asInstanceOf[BricsAutomaton]))
  val termSet = allInitialConstraints.groupBy(_._1).map(_._1)
  val productInitialConstraints = termSet zip autSet.map(BricsAutomaton.productSpecially(_))
  val debug = productInitialConstraints
  //////////////////////////////////////////////////////////////////////////////


  private val constraintStores = new MHashMap[Term, ConstraintStore]

  def findModel : Option[Map[Term, Seq[Int]]] = {
      for (t <- allTerms)
        constraintStores.put(t, newStore(t))

      // check whether initialConstraints are consistent
      for ((t, aut) <- productInitialConstraints) {
        // add term's aut to constraints , TODO： watch this ---------------------------------------------
        constraintStores(t).assertConstraint(aut) match {
          case Some(_) => return None
          case None    => // nothing
        }
        // huzi add
        // Initially, add allInitialConstraints to AtomConstraints
        AtomConstraints.addConstraints(TermConstraint(t,aut))
      }

    val funAppList =
      (for ((apps, res) <- sortedFunApps;
            (op, args) <- apps)
       yield (op, args, res)).toList


    try {
      dfExplore(funAppList)
      None
    } catch {
      case FoundModel(model) => Some(model)
    }
  }

  private def evalTerm(t : Term)(model : SimpleAPI.PartialModel)
                      : Option[IdealInt] = t match {
    case c : ConstantTerm =>
      model eval c
    case OneTerm =>
      Some(IdealInt.ONE)
    case lc : LinearCombination => {
      val terms = for ((coeff, t) <- lc) yield (coeff, evalTerm(t)(model))
      if (terms forall { case (_, None) => false
                         case _ => true })
        Some((for ((coeff, Some(v)) <- terms) yield (coeff * v)).sum)
      else
        None
    }
  }

// get product of all (term, aut) in cons, result is final producted bricsAutomaton of each term.  
  private def getProductAuts(cons : ArrayBuffer[TermConstraint]) : Seq[BricsAutomaton] = {
    // not test, maybe wrong
    val atomSeq : Seq[ArrayBuffer[BricsAutomaton]] =
      cons.groupBy{case TermConstraint(aTerm, _) => aTerm}.map(_._2)
        .map{case a => a.map{case TermConstraint(_,aut)=>AtomicStateAutomatonAdapter.intern(aut).asInstanceOf[BricsAutomaton]}}
        .toSeq
    val res = atomSeq.map(BricsAutomaton.product(_))
    res
  }

  // get parikhImage of each bricsAutomaton in auts
  private def getAutsParikhImage(auts : Seq[BricsAutomaton]) : List[Formula] = {
    (auts.map{aut => aut.parikhImage}).toList
  }

  /**
   * input topological funclist, return the conflict set, or throw FindModel
   * 
   */
  private def dfExplore(apps : List[(PreOp, Seq[Term], Term)]
                        )
                      : ConflictSet = apps match {

    case List() => {
      // // we are finished and just have to construct a model
      // if findModel, throw FindModel, else return List() stand for Unknow
      val model = new MHashMap[Term, Seq[Int]]
      if(!strictLengths)      
        // there is no int constraints
        throw FoundModel(model.toMap)

      val tmpBuffer = AtomConstraints.constraints.clone()

      AtomConstraints.constraints.foreach{
        case TermConstraint(term, a) => {
          if(notAtomTermSet(term)){
            tmpBuffer -= TermConstraint(term, a)
          }
        }
      }

      val finalCons = getProductAuts(tmpBuffer)
      val parikhIntFormula = getAutsParikhImage(finalCons).map(Internal2InputAbsy(_))
      
      SimpleAPI.withProver{ p=>
        import p._
        println("begin to compute parikh image")
        val constantTermSet = new MHashSet[ConstantTerm]()
        parikhIntFormula.foreach{case formula => constantTermSet ++= SymbolCollector.constantsSorted(formula)}
        parikhIntFormula.foreach(addAssertion(_))

        // println("output parikh formula")
        // parikhIntFormula.foreach{case formula => {SMTLineariser((formula)); println()}}

        // the input int constraints
        val inputIntFormula = IntConstraintStore()
        constantTermSet ++= SymbolCollector constantsSorted Internal2InputAbsy(inputIntFormula)
        addAssertion(inputIntFormula)

        for(i <- 0 to LCStack.size-1) {
          val preOpIntFormula = LCStack(i)
          preOpIntFormula().foreach{
            case a => constantTermSet ++= SymbolCollector.constantsSorted((a))
          }
          preOpIntFormula().foreach(addAssertion(_))
        }
        addConstantsRaw(constantTermSet)
        println(???)
        ??? match {
          case ProverStatus.Sat => throw FoundModel(model.toMap)
          // return List() to stand for Unknow
          case ProverStatus.Unsat => return  List()
        }
      }
      // -----------------------------------------------------------------------

    }
    case (op, args, res) :: otherApps =>
      dfExploreOp(op, args, res, constraintStores(res).getContents,
                  otherApps)
  }

  private def dfExploreOp(op : PreOp,
                          args : Seq[Term],
                          res : Term,
                          resConstraints : List[Automaton],
                          nextApps : List[(PreOp, Seq[Term], Term)]
                          )
                        : ConflictSet = resConstraints match {
    case List() =>
      dfExplore(nextApps)

    case resAut :: otherAuts => {
      ap.util.Timeout.check

      val argConstraints =
        for (a <- args) yield constraintStores(a).getCompleteContents
      val collectedConflicts = new LinkedHashSet[TermConstraint]

      // huzi modify
      val (newConstraintsWithLinear, argDependencies) = 
        measure("pre-op") { op(argConstraints, resAut) }

      while (measure("pre-op hasNext") {newConstraintsWithLinear.hasNext}) {

        val (argCS, lC) = newConstraintsWithLinear.next

        // huzi add
        AtomConstraints.push
        LCStack push lC
        for (a <- args){
          constraintStores(a).push
        }


        try {
          val newConstraints = new MHashSet[TermConstraint]

          var consistent = true
          for ((a, aut) <- args zip argCS)
            if (consistent) {
              newConstraints += TermConstraint(a, aut)
              // huzi add 
              AtomConstraints.addConstraints(TermConstraint(a,aut))

              constraintStores(a).assertConstraint(aut) match {
                case Some(conflict) => {
                  consistent = false

                  assert(!Seqs.disjointSeq(newConstraints, conflict))
                  collectedConflicts ++=
                    (conflict.iterator filterNot newConstraints)
                }
                case None => // nothing
              }
            }



          if (consistent) {
            val conflict = dfExploreOp(op, args, res, otherAuts, nextApps)
            // huzi add
            if(conflict.isEmpty)
              // Unknow, do nothing
              conflict
            else if (Seqs.disjointSeq(newConstraints, conflict)) {
              // we can jump back, because the found conflict does not depend
              // on the considered function application
//println("backjump " + (conflict map { case TermConstraint(t, aut) => (t, aut.hashCode) }))
              return conflict
            }
            collectedConflicts ++= (conflict.iterator filterNot newConstraints)
          }
        } finally {
          for (a <- args) {
            constraintStores(a).pop
          }
          AtomConstraints.pop
          LCStack.pop
        }
      }
      // while end--------------------------------------------------------------------------------------------------------


      if (needCompleteContentsForConflicts)
        collectedConflicts ++=
          (for (aut <- constraintStores(res).getCompleteContents)
           yield TermConstraint(res, aut))
      else
        collectedConflicts += TermConstraint(res, resAut)

      collectedConflicts ++=
        (for ((t, auts) <- args.iterator zip argDependencies.iterator;
              aut <- auts.iterator)
         yield TermConstraint(t, aut))

      collectedConflicts.toSeq
    }
  }
  protected def newStore(t : Term) : ConstraintStore

  protected val needCompleteContentsForConflicts : Boolean

}


/**
 * Version of exploration that keeps automata separate and avoids computation
 * of products. No caching yet
 */
class LazyExploration(_funApps : Seq[(PreOp, Seq[Term], Term)],
                      // huzi add 
                      _intFunApps : Seq[(PreOp, Seq[Term], Term)],
                      // huzi add
                      _initialConstraints : Seq[(Term, Automaton)],
                      // _lengthProver : Option[SimpleAPI],
                      _lengthVars : Map[Term, Term],
                      _strictLengths : Boolean)
      extends Exploration(_funApps, _intFunApps, _initialConstraints,
                          _lengthVars, _strictLengths) {

  import Exploration._

  protected val needCompleteContentsForConflicts : Boolean = false

  private val stores = new ArrayBuffer[Store]

  // Combinations of automata that are known to have empty intersection
  private val inconsistentAutomata = new ArrayBuffer[Seq[Automaton]]

  private def addIncAutomata(auts : Seq[Automaton]) : Unit = {
    inconsistentAutomata += auts
//    println("Watching " + inconsistentAutomata.size + " sets of inconsistent automata")
    val ind = inconsistentAutomata.size - 1
    for (s <- stores) {
      val r = s.watchAutomata(auts, ind)
      assert(r)
    }
  }

  protected def newStore(t : Term) : ConstraintStore = new Store(t)

  private class Store(t : Term) extends ConstraintStore {
    //  constraints about t, stored by ArrayBuffer
    private val constraints = new ArrayBuffer[Automaton]
    //  constraints about t, stored by MHashSet
    private val constraintSet = new MHashSet[Automaton]
    // store constraints.size, for push and pop operation 
    private val constraintStack = new ArrayStack[Int]

    // Map from watched automata to the indexes of
    // <code>inconsistentAutomata</code> that is watched
    private val watchedAutomata = new MHashMap[Automaton, List[Int]]

    // Add a new entry to <code>watchedAutomata</code>; return
    // <code>false</code> in case the set of new automata is a subset of the
    // asserted constraints
    def watchAutomata(auts : Seq[Automaton], ind : Int) : Boolean =
      // TODO: we should randomise at this point! 
      // NOW : choose the first automata not in constraintSet, and add it to 
      // watchedAutomata, or just return false.
      (auts find { a => !(constraintSet contains a) }) match {
        case Some(aut) => {
          watchedAutomata.put(aut,
                              ind :: watchedAutomata.getOrElse(aut, List()))
          true
        }
        case None =>
          false
      }

    def push : Unit = constraintStack push constraints.size

    def pop : Unit = {
      val oldSize = constraintStack.pop
      while (constraints.size > oldSize) {
        constraintSet -= constraints.last
        constraints reduceToSize (constraints.size - 1)
      }
    }

    def assertConstraint(aut : Automaton) : Option[ConflictSet] =
      if (constraintSet contains aut) {
        None
      } else {
        // huzi : the logic below maybe wrong!
        var potentialConflicts =
          (watchedAutomata get aut) match {
            case Some(incAuts) => {
              // need to find new watched automata for the found conflicts
              watchedAutomata -= aut
              incAuts
            }
            case None =>
              List()
          }

        while (!potentialConflicts.isEmpty) {
          val autInd = potentialConflicts.head

          if (!watchAutomata(inconsistentAutomata(autInd), autInd)) {
            // constraints have become inconsistent!  
            // huzi : is this really happen? line 653(the fisrt if else) guarantee that
            // constraintSet do not contains aut, so watchAutomata always return true in this
            // code block

            watchedAutomata.put(aut, potentialConflicts)
            println("Stored conflict applies!")
            return Some(for (a <- inconsistentAutomata(autInd).toList)
                        yield TermConstraint(t, a))
          }

          potentialConflicts = potentialConflicts.tail
        }

        // find inconsistent constraints
        measure("AutomataUtils.findUnsatCore") { AutomataUtils.findUnsatCore(constraints, aut) } match {
          case Some(core) => {
            addIncAutomata(core)
            Some(for (a <- core.toList) yield TermConstraint(t, a))
          }
          case None => {
            constraints += aut
            constraintSet += aut
            val c = TermConstraint(t, aut)
//            addLengthConstraint(c, List(c))
            None
          }
        }
      }

    def getContents : List[Automaton] =
      constraints.toList
    def getCompleteContents : List[Automaton] =
      constraints.toList

    private def intersection : Automaton = constraints reduceLeft (_ & _)


    def getAcceptedWord : Seq[Int] =
      constraints match {
        case Seq() => List()
        case auts  => intersection.getAcceptedWord.get
      }

    def getAcceptedWordLen(len : Int) : Seq[Int] =
      constraints match {
        case Seq() => for (_ <- 0 until len) yield 0
        case auts  => AutomataUtils.findAcceptedWord(auts, len).get
      }
  }

}


object AtomConstraints {

  val constraints = new ArrayBuffer[TermConstraint]
  val constraintsStack = new ArrayStack[Int]

  def push : Unit = constraintsStack push constraints.size
  def pop : Unit = {
    val oldSize = constraintsStack.pop
    constraints reduceToSize oldSize
  }
  def addConstraints(cons : TermConstraint){
    constraints += cons 
  }
  def deleConstraints(cons : TermConstraint){
    constraints -= cons
  }
}