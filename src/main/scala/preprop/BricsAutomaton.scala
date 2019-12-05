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

import java.io.{FileWriter, PrintWriter}

import strsolver.Regex2AFA
import ap.terfor.Term
import ap.terfor.preds.PredConj
import ap.parser.{IConstant, ITerm, InputAbsy2Internal, Internal2InputAbsy}
import dk.brics.automaton.{BasicAutomata, BasicOperations, RegExp, Transition, Automaton => BAutomaton, State => BState}

import scala.collection.JavaConversions.{asScalaIterator, iterableAsScalaIterable}
import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, HashSet => MHashSet, LinkedHashSet => MLinkedHashSet, MultiMap => MMultiMap, Set => MSet, Stack => MStack, TreeSet => MTreeSet}
import scala.collection.immutable.List
import java.util.{List => JList}

import scala.collection.JavaConverters._

object BricsAutomaton {
  private def toBAutomaton(aut : Automaton) : BAutomaton = aut match {
    case that : BricsAutomaton =>
      that.underlying
    case that : AtomicStateAutomatonAdapter[_] =>
      toBAutomaton(that.internalise)
    case _ =>
      throw new IllegalArgumentException
  }

  def apply(c : Term, context : PredConj) : BricsAutomaton = {
    val converter = new Regex2AFA(context)
    new BricsAutomaton(converter.buildBricsAut(c))
  }

  def apply() : BricsAutomaton = new BricsAutomaton(new BAutomaton)

  /**
   * Build brics automaton from a regular expression in brics format
   */
  def apply(pattern: String): BricsAutomaton =
    new BricsAutomaton(new RegExp(pattern).toAutomaton(true))

  /**
   * Build brics automaton that accepts exactly the given word
   */
  def fromString(str : String) : BricsAutomaton =
    new BricsAutomaton(BasicAutomata makeString str)

//  def makeEmptyString() : BricsAutomaton =
//    new BricsAutomaton(BasicAutomata makeEmptyString())
  /**
   * A new automaton that accepts any string
   */
  def makeAnyString() : BricsAutomaton = {
//      new BricsAutomaton(BAutomaton.makeAnyString)
    val builder = new BricsAutomatonBuilder
    val initState = builder.getNewState
    val Sigma = builder.LabelOps.sigmaLabel
    builder.setInitialState(initState)
    builder.setAccept(initState, true)
    builder.addTransition(initState, Sigma, initState)
    builder.getAutomaton

  }


  // huzi add -------------------------------------------
  /**
    * concatenate
    */
  def concat(auts : List[BAutomaton]) : Automaton = {
    val aut = BasicOperations.concatenate(auts.asJava)
    aut.minimize()
    aut.restoreInvariant
    new BricsAutomaton(aut)
  }

  // get product of auts whose registers is NULL
  def productSpecially(auts: Seq[Automaton]): BricsAutomaton = {
    new BricsAutomaton(toBAutomaton(auts.reduceLeft(_ & _)))
  }

  val MaxSimultaneousProduct = 5

  def product(auts: Seq[BricsAutomaton]): BricsAutomaton = {
    if (auts.size == 0)
      return (BricsAutomaton.makeAnyString)

    if (auts.size == 1)
      return auts.head

    val firstSlice = auts
      .grouped(MaxSimultaneousProduct)
      .map(fullProduct(_))
      .toSeq

    if (firstSlice.size == 1)
      return firstSlice(0)
    else
      return product(firstSlice)
  }

  def fullProduct(auts: Seq[BricsAutomaton]): BricsAutomaton = {
    val head    = auts.head
    val builder = head.getBuilder

    val registers = auts.flatMap(_.registers).toList

    val initState = builder.initialState
    // from new states to list of old
    val sMap = new MHashMap[head.State, List[Any]]
    // from list of old to new states
    val sMapRev = new MHashMap[List[Any], head.State]

    val initStates = (auts.map(_.initialState)).toList
    sMap += initState     -> initStates
    sMapRev += initStates -> initState

    val worklist = new MStack[(head.State, List[Any])]
    worklist push ((initState, initStates))

    val seenlist = MHashSet[List[Any]]()
    seenlist += initStates

    builder.setAccept(initState, auts forall { aut =>
      aut.isAccept(aut.initialState)
    })

    var checkCnt = 0

    while (!worklist.isEmpty) {
      val (ps, ss) = worklist.pop()

      // collects transitions from (s, ss)
      // lbl = (min, max) is current range
      // vector is current vector
      // sp and ssp are s' and ss' (ss' is reversed for efficiency)
      // ss are elements of ss from which a transition is yet to be
      // searched
      def addTransitions(
          lbl: head.TLabel,
          vector: List[Int],
          ssp: List[Any],
          remAuts: List[BricsAutomaton],
          ss: List[Any]
      ): Unit = {
        checkCnt = checkCnt + 1
        if (checkCnt % 1000 == 0)
          ap.util.Timeout.check
        ss match {
          case Seq() => {
            val nextState = ssp.reverse
            if (!seenlist.contains(nextState)) {
              val nextPState = builder.getNewState
              val isAccept = (auts.iterator zip nextState.iterator) forall {
                case (aut, s) => aut.isAccept(s.asInstanceOf[aut.State])
              }
              builder.setAccept(nextPState, isAccept)
              sMap += nextPState   -> nextState
              sMapRev += nextState -> nextPState
              worklist.push((nextPState, nextState))
              seenlist += nextState
            }
            val nextPState = sMapRev(nextState)
            // add vector
            builder.addTransition(ps, lbl, nextPState, vector)
          }
          case _state :: ssTail => {
            val aut :: autsTail = remAuts
            val state           = _state.asInstanceOf[aut.State]

            aut.outgoingTransitions(state) foreach {
              case (s, nextLbl) => {
                val newLbl =
                  builder.LabelOps
                    .intersectLabels(lbl, nextLbl.asInstanceOf[head.TLabel])
                // this sort maybe wrong
                val vect = vector ::: aut.etaMap((state, nextLbl, s))
                for (l <- newLbl)
                  addTransitions(l, vect, s :: ssp, autsTail, ssTail)
              }
            }
          }
        }
      }

      addTransitions(
        builder.LabelOps.sigmaLabel,
        List(),
        List(),
        auts.toList,
        ss
      )
    }

    val res = builder.getAutomaton
    res.addEtaMaps(builder.etaMap)
    res.setRegisters(registers)
// have not removeDeadTranstions
    res
  }
}

object BricsTLabelOps extends TLabelOps[(Char, Char)] {

  val vocabularyWidth: Int = 16 // really?

  /**
    * Check whether the given label accepts any letter
    */
  def isNonEmptyLabel(label: (Char, Char)): Boolean =
    label._1 <= label._2

  /**
    * Label accepting all letters
    */
  // val sigmaLabel : (Char, Char) =
  //   (Char.MinValue, Char.MaxValue)

  //huzi modify, ascii char
  val sigmaLabel: (Char, Char) =
    (Char.MinValue, Char.MaxValue)

  def singleton(a: Char) = (a, a)

  /**
    * Intersection of two labels
    */
  def intersectLabels(
      l1: (Char, Char),
      l2: (Char, Char)
  ): Option[(Char, Char)] = {
    Option(l1._1 max l2._1, l1._2 min l2._2).filter(isNonEmptyLabel(_))
  }

  /**
    * True if labels overlap
    */
  def labelsOverlap(l1: (Char, Char), l2: (Char, Char)): Boolean = {
    val (min1, max1) = l1
    val (min2, max2) = l2
    (min2 <= max1 && max2 >= min1)
  }

  /**
    * Can l represent a?
    */
  def labelContains(a: Char, l: (Char, Char)): Boolean = {
    val (min, max) = l
    (min <= a && a <= max)
  }

  /**
    * Enumerate all letters accepted by a transition label
    */
  def enumLetters(label: (Char, Char)): Iterator[Int] =
    for (c <- (label._1 to label._2).iterator) yield c.toInt

  /**
    * Remove a given character from the label.  E.g. [1,10] - 5 is
    * [1,4],[6,10]
    */
  def subtractLetter(a: Char, lbl: (Char, Char)): Iterable[(Char, Char)] = {
    val (min, max) = lbl
    if (min <= a && a <= max) {
      // surely a cuter solution than this exists...
      var res = List[(Char, Char)]()
      if (min < a)
        res = (min, (a - 1).toChar) :: res
      if (a < max)
        res = ((a + 1).toChar, max) :: res
      res
    } else {
      Seq(lbl)
    }
  }

  /**
    * Shift characters by n, do not wrap.  E.g. [1,2].shift 3 = [4,5]
    */
  def shift(lbl: (Char, Char), n: Int): (Char, Char) = {
    val (cmin, cmax) = lbl
    (
      Math.max(Char.MinValue, cmin + n).toChar,
      Math.min(Char.MaxValue, cmax + n).toChar
    )
  }

  /**
    * Get representation of interval [min,max]
    */
  def interval(min: Char, max: Char): (Char, Char) = (min, max)
}

class BricsTLabelEnumerator(labels: Iterator[(Char, Char)]) extends TLabelEnumerator[(Char, Char)] {

  /**
    * Keep track of disjoint labels for fast range lookups in
    * enumLabelOverlap.  Access with getDisjointLabels.
    */
  private lazy val disjointLabels: MTreeSet[(Char, Char)] =
    calculateDisjointLabels

  /**
    * Like disjoint labels but covers whole alphabet including internal
    * char.
    */
  private lazy val disjointLabelsComplete: List[(Char, Char)] =
    calculateDisjointLabelsComplete

  /**
    * Enumerate all labels with overlaps removed.
    * E.g. for min/max labels [1,3] [5,10] [8,15] would result in [1,3]
    * [5,8] [8,10] [10,15]
    */
  def enumDisjointLabels: Iterable[(Char, Char)] =
    disjointLabels.toIterable

  /**
    * Enumerate all labels with overlaps removed such that the whole
    * alphabet is covered (including internal characters)
    * E.g. for min/max labels [1,3] [5,10] [8,15] would result in [1,3]
    * [4,4] [5,7] [8,10] [11,15] [15,..]
    */
  def enumDisjointLabelsComplete: Iterable[(Char, Char)] =
    disjointLabelsComplete

  /**
    * iterate over the instances of lbls that overlap with lbl
    */
  def enumLabelOverlap(lbl: (Char, Char)): Iterable[(Char, Char)] = {
    val (lMin, lMax) = lbl
    disjointLabels
      .from((lMin, Char.MinValue))
      .to((lMax, Char.MaxValue))
      .toIterable
  }

  /**
    * Takes disjoint enumeration and splits it at the point defined by
    * Char.  E.g. [1,10] split at 5 is [1,4][5][6,10]
    */
  def split(a: Char): TLabelEnumerator[(Char, Char)] =
    new BricsTLabelEnumerator(disjointLabels.iterator ++ Iterator((a, a)))

  private def calculateDisjointLabels(): MTreeSet[(Char, Char)] = {
    var disjoint = new MTreeSet[(Char, Char)]()

    val mins  = new MTreeSet[Char]
    val maxes = new MTreeSet[Char]
    for ((min, max) <- labels) {
      mins += min
      maxes += max
    }

    val imin = mins.iterator
    val imax = maxes.iterator

    if (!imin.hasNext)
      return disjoint

    var curMin  = imin.next
    var nextMax = imax.next
    while (imin.hasNext) {
      val nextMin = imin.next
      if (nextMin <= nextMax) {
        disjoint += ((curMin, (nextMin - 1).toChar))
        curMin = nextMin
      } else {
        disjoint += ((curMin, nextMax))
        curMin = nextMin
        nextMax = imax.next
      }
    }

    disjoint += ((curMin, nextMax))
    curMin = (nextMax + 1).toChar

    while (imax.hasNext) {
      val nextMax = imax.next
      disjoint += ((curMin, nextMax))
      curMin = (nextMax + 1).toChar
    }

    disjoint
  }

  private def calculateDisjointLabelsComplete(): List[(Char, Char)] = {
    val labelsComp = disjointLabels.foldRight(List[(Char, Char)]()) {
      case ((min, max), Nil) => {
        // using Char.MaxValue since we include internal chars
        if (max < Char.MaxValue)
          List((min, max), ((max + 1).toChar, Char.MaxValue))
        else
          List((min, max))
      }
      case ((min, max), (minLast, maxLast) :: lbls) => {
        val minLastPrev = (minLast - 1).toChar
        if (max < minLastPrev)
          (min, max) :: ((max + 1).toChar, minLastPrev) :: (minLast, maxLast) :: lbls
        else
          (min, max) :: (minLast, maxLast) :: lbls
      }
    }
    if (Char.MinValue < labelsComp.head._1) {
      val nextMin = (labelsComp.head._1 - 1).toChar
      (Char.MinValue, nextMin) :: labelsComp
    } else {
      labelsComp
    }
  }
}

/**
  * Wrapper for the BRICS automaton class
  */
class BricsAutomaton(val underlying: BAutomaton) extends AtomicStateAutomaton {

  import BricsAutomaton.toBAutomaton

  type State  = BState
  type TLabel = (Char, Char)

  override val LabelOps = BricsTLabelOps

  override def toString: String = underlying.toString

  // hu zi add ---------------------------------------------------------------------------------------------------------------
//  val registers : ArrayBuffer[ITerm]= ArrayBuffer()  // or maybe ArrayBuffer[ConstantTerm]
  // registers += AllocRegisterTerm()  //debug
  // (q', σ, q, η) tuple, stored as a map
  val etaMap = new MHashMap[(State, TLabel, State), List[Int]]

  addEtaMapsDefault

  /**
    * get parikh iamge of BricsAutomaton
    */
  import ap.terfor.{Formula, Term, TerForConvenience, TermOrder, OneTerm, VariableTerm}
  import scala.collection.mutable.{
    BitSet => MBitSet,
    HashMap => MHashMap,
    HashSet => MHashSet,
    ArrayStack
  }
  import ap.terfor.linearcombination.LinearCombination
  import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
  import ap.basetypes.IdealInt
  import ap.PresburgerTools

  override def parikhImage: Formula =
    Exploration.measure("length abstraction") {
      import TerForConvenience._

      val constantSeq    = registers.map { case IConstant(c) => c }
      implicit val order = TermOrder.EMPTY.extend(constantSeq)

      // val a = registers.map(InputAbsy2Internal(_,TermOrder.EMPTY)).toSeq

      val stateSeq    = states.toIndexedSeq
      val state2Index = stateSeq.iterator.zipWithIndex.toMap

      // preStates(to): =  [(from, (from, label, to))]
      lazy val preStates = {
        val preStates =
          Array.fill(stateSeq.size)(new ArrayBuffer[(Int, List[Int])])

        for ((from, label, to) <- transitions) {
          val vector = etaMap((from, label, to))
          preStates(state2Index(to)) += ((state2Index(from), vector))
        }

        preStates
      }
      lazy val transPreStates = {
        val transPreStates = Array.fill(stateSeq.size)(new MBitSet)

        // transPreStates clone from preStates
        for ((array, s2) <- preStates.iterator zip transPreStates.iterator)
          for ((s1, _) <- array)
            s2 += s1

        for ((s, n) <- transPreStates.iterator.zipWithIndex)
          s += n

        var changed = false
        do {
          for (outgoing <- transPreStates) {
            val oldSize = outgoing.size

            for (target <- outgoing)
              outgoing |= transPreStates(target)

            changed = outgoing.size > oldSize
          }
        } while (changed)

        transPreStates
      }
      val initialStateInd = state2Index(initialState)

      ////////////////////////////////////////////////////////////////////////////

      // disjunction of formulas
      disjFor(
        for (finalState <- acceptingStates)
          yield {
            val finalStateInd = state2Index(finalState)
            val refStates     = transPreStates(finalStateInd)

            // FIXME: remove self-loops maybe?
            // FIXME: the initial state should appear (at least) twice now?
            // FIXME: No need for concatenation: not ordered
            // [to, Option[from] [labels]]
            val productions: List[(Int, Option[Int], List[Int])] =
              (if (refStates contains initialStateInd)
                 List((initialStateInd, None, List()))
               else List()) ::: // FIXME: why concat?
                (for (state    <- refStates.iterator;
                      preState <- preStates(state))
                  yield (state, Some(preState._1), preState._2)).toList

            val prodVars = productions.view.zipWithIndex.map {
              case (_, i) => v(i)
            }
            val zVars = refStates
              .zip(Stream from prodVars.size)
              .map {
                case (state, index) =>
                  state -> v(index)
              }
              .toMap

            // Generate 0 - 2 variable -> coefficient * term mappings from a
            // transition , eg.
            // A TRANS TO would give
            //   [A -> 1 * Y_A->B,
            //    B -> -1 * Y_A->B]
            def stateTermsFromTransition(
                t: ((Int, Option[Int], Any), VariableTerm)
            ): List[(Int, (IdealInt, VariableTerm))] =
              t match {
                // Ignore self-loops:
                case ((to, from, _), _) if from == to => List()
                case ((to, None, _), v)               => List(to -> (IdealInt.MINUS_ONE, v))
                case ((to, Some(from), _), v) =>
                  List(to -> (IdealInt.MINUS_ONE, v), from -> (IdealInt.ONE, v))
              }

            // Translate the weird output of groupBy to actual linear
            // combinations using the coefficients generated by
            // stateTermsFromTransition. For the final state, add +1 to the
            // terms as per the algorithm.
            def termsToLinearEq(
                st: ((Int, List[(Int, (IdealInt, VariableTerm))]))
            ): LinearCombination = {
              val (state, state_terms) = st
              val terms                = state_terms.map(_._2)

              if (state == finalStateInd)
                LinearCombination((IdealInt.ONE, OneTerm) :: terms, order)
              else LinearCombination(terms, order)
            }

            // [((to, from, registers), Z_prod)]
            val prodsWithVars = productions.zip(prodVars)

            // equations relating the production counters
            // consistent
            // Transition equations (for non-terminals)
            // [Eq(0/1  +/- Y_transition_1, ..., +/- Y_transition_n),
            // ... ] (+ for from, - for to), one per terminal involved
            // NOTE: This is backwards compared to the paper: 1 on final, reversed sign on from/to
            val prodEqs = prodsWithVars
              .map(stateTermsFromTransition)
              .flatten
              .groupBy(_._1)        // group by state
              .map(termsToLinearEq) // translate to each state's equation
              .toList

            // registers

            // Create the terms for the register equation:
            def makeRegisterTerms(ri: (ITerm, Int)): List[(IdealInt, Term)] = {
              val (r, i) = ri
              val prodTerms = prodsWithVars
                .filter { case ((_, from, _), _) => from != None }
                .map {
                  case ((_, _, regs), prodVar) => (IdealInt(regs(i)), prodVar)
                }

              (IdealInt.MINUS_ONE, InputAbsy2Internal(r, order)) :: prodTerms
            }

            // for each register, generate a linear combination of -1 * r +
            // [y_A->B * s(r)], where s(r) for each register r, where s(r) is
            // the...state of register r at state s.
            val rEqs = registers.zipWithIndex
              .map(makeRegisterTerms)
              .map(terms => LinearCombination(terms, order))
              .toList

            val entryZEq = zVars(finalStateInd) - 1

            val allEqs = eqZ(entryZEq :: prodEqs ::: rEqs)

            val prodNonNeg = prodVars >= 0

            // Production implications: either we didn't use a production, or
            // its corresponding target is greater than zero.
            val prodImps = prodsWithVars
              .filter{case ((to, _, _), _) => to != finalStateInd}
              .map{case ((to, _, _), prodVar) => (prodVar === 0) | zVars(to) > 0}
              .toList

            // connective
            val zImps =
              (for (state <- refStates.iterator; if state != finalStateInd)
                yield {
                  disjFor(
                    Iterator(zVars(state) === 0) ++
                      (for (((to, from, _), prodVar) <- productions.iterator zip prodVars.iterator;
                            if from contains state)
                        yield conj(
                          zVars(state) === zVars(to) + 1,
                          geqZ(List(prodVar - 1, zVars(to) - 1))
                        ))
                  )
                }).toList

            val matrix =
              conj(allEqs :: prodNonNeg :: prodImps ::: zImps)
            val rawConstraint =
              exists(prodVars.size + zVars.size, matrix)

            val constraint =
              ap.util.Timeout.withTimeoutMillis(1000) {
                // best-effort attempt to get a quantifier-free version of the
                // length abstraction
                PresburgerTools.elimQuantifiersWithPreds(rawConstraint)
              } {
                ReduceWithConjunction(Conjunction.TRUE, order)(rawConstraint)
              }

            constraint
          }
      )
    }

  /**
    * addEtaMap, vector.length must equal to registers.length
    */
  def addEtaMap(transition: (State, TLabel, State), vector: List[Int]): Unit = {
    etaMap += (transition -> vector)
  }

  /**
    * addEtaMaps, input is a hashmap
    */
  def addEtaMaps(map: MHashMap[(State, TLabel, State), List[Int]]): Unit = {
    etaMap ++= map
  }

  /**
    * addEtaMapDefault, the default vector is considered to be 0
    */
  def addEtaMapDefault(transition: (State, TLabel, State)): Unit = {
    val vector = List.fill(registers.length)(0)
    addEtaMap(transition, vector)
  }

  /**
    * addEtaMapsDefault
    */
  def addEtaMapsDefault(): Unit = {
    for ((s1, l, s2) <- this.transitions) {
      addEtaMapDefault((s1, l, s2))
    }
  }
  val debugTransitions = {
    (for ((s1, l, s2) <- this.transitions) yield (s1, l, s2)).toList
  }

  /**
    * register op:
    */
  def addNewRegister(num: Int): Unit = {
    for (i <- 1 to num)
      registers += AllocRegisterTerm()
  }
  def addRegisters(rs: ArrayBuffer[ITerm]): Unit = {
    registers ++= rs
  }
  def setRegisters(rs: ArrayBuffer[ITerm]): Unit = {
    registers.clear()
    registers ++= rs
  }
  def setRegisters(rs: List[ITerm]): Unit = {
    registers.clear()
    registers ++= rs
  }

  /**
    * cloneRegisters : clone register, use the different token
    */
  def cloneRegisters(): ArrayBuffer[ITerm] = {
    val res: ArrayBuffer[ITerm] = ArrayBuffer()
    for (i <- registers) {
      res += AllocRegisterTerm()
    }
    res
  }

  def removeDeadTranstions(): Unit = {}

  // print this aut
//  def printAut() : Unit = {
//    val out = new PrintWriter(new FileWriter("tmp.txt", true))
//    val statesIndex = states.zipWithIndex.toMap
//    out.println("#automata:")
//    out.println("#states: "+states.size)
//    out.println("#init: "+ statesIndex(initialState))
//    out.print("#final: ")
//    acceptingStates.foreach{case state => print(statesIndex(state) + ",")}
//    out.println()
//    out.println("#transitons: ")
//    etaMap.foreach{case ((from, (charmin,charmax), to),vector) =>
//      out.println(statesIndex(from)+";"+statesIndex(to)+";"+charmin.toInt+";"+charmax.toInt+";"+vector)}
//    out.print("#register: ")
//    registers.foreach{case r => out.print(r + ",")}
//    out.println()
//    out.close()
//  }

  // hu zi add ------------------------------------------------------------------------------------------------------

  /**
    * Union
    */
  def |(that: Automaton): Automaton =
    new BricsAutomaton(
      BasicOperations.union(this.underlying, toBAutomaton(that))
    )

  /**
    * Intersection
    */
  def &(that: Automaton): Automaton = {
    val productAut =
      BasicOperations.intersection(this.underlying, toBAutomaton(that))
    productAut.minimize()
    new BricsAutomaton(productAut)
  }

  /**
    * Complementation
    */
  def unary_! : Automaton =
    new BricsAutomaton(BasicOperations.complement(this.underlying))

  /**
    * Check whether this automaton describes the empty language.
    */
  def isEmpty: Boolean =
    underlying.isEmpty

  /**
    * Check whether the automaton accepts a given word.
    */
  def apply(word: Seq[Int]): Boolean =
    BasicOperations.run(
      this.underlying,
      SeqCharSequence(for (c <- word.toIndexedSeq) yield c.toChar).toString
    )

  /**
    * Iterate over automaton states, return in deterministic order
    */
  lazy val states: Iterable[State] = {
    // do this the hard way to give a deterministic ordering
    val worklist   = new MStack[State]
    val seenstates = new MLinkedHashSet[State]

    worklist.push(initialState)
    seenstates.add(initialState)

    while (!worklist.isEmpty) {
      val s = worklist.pop

      val dests = new MHashMap[TLabel, MSet[State]] with MMultiMap[TLabel, State]

      for ((to, _) <- outgoingTransitions(s)) {
        if (!seenstates.contains(to)) {
          worklist.push(to)
          seenstates += to
        }
      }
    }

    seenstates
  }

  /**
    * The unique initial state
    */
  lazy val initialState: State = underlying.getInitialState

  /**
    * Given a state, iterate over all outgoing transitions, try to be
    * deterministic
    */
  def outgoingTransitions(from: State): Iterator[(State, TLabel)] = {
    val dests = new MHashMap[TLabel, MSet[State]] with MMultiMap[TLabel, State]

    for (t <- from.getTransitions)
      dests.addBinding((t.getMin, t.getMax), t.getDest)

    val outgoing = new MLinkedHashSet[(State, TLabel)]

    for (lbl <- dests.keys.toList.sorted) {
      for (s <- dests(lbl)) {
        outgoing += ((s, lbl))
      }
    }

    outgoing.iterator
  }

  /**
    * The set of accepting states
    */
  lazy val acceptingStates: Set[State] =
    (for (s <- states; if s.isAccept) yield s).toSet

  lazy val labelEnumerator =
    new BricsTLabelEnumerator(for ((_, lbl, _) <- transitions) yield lbl)

  /*
   * Get any word accepted by this automaton, or <code>None</code>
   * if the language is empty
   */
  def getAcceptedWord: Option[Seq[Int]] =
    (this.underlying getShortestExample true) match {
      case null => None
      case str  => Some(for (c <- str) yield c.toInt)
    }

  def isAccept(s: State): Boolean = s.isAccept

  def toDetailedString: String = underlying.toString

  def getBuilder: BricsAutomatonBuilder = new BricsAutomatonBuilder

  def getTransducerBuilder: BricsTransducerBuilder = BricsTransducer.getBuilder
}

/**
  * For constructing manually (immutable) BricsAutomaton objects
  */
class BricsAutomatonBuilder
    extends AtomicStateAutomatonBuilder[
      BricsAutomaton#State,
      BricsAutomaton#TLabel
    ] {
  val LabelOps: TLabelOps[BricsAutomaton#TLabel] = BricsTLabelOps

  var minimize = true

  val baut: BAutomaton = {
    val baut = new BAutomaton
    baut.setDeterministic(false)
    baut
  }

  val etaMap =
    new MHashMap[
      (BricsAutomaton#State, BricsAutomaton#TLabel, BricsAutomaton#State),
      List[Int]
    ]

  /**
    * The initial state of the automaton being built
    */
  def initialState: BricsAutomaton#State = baut.getInitialState

  /**
    * By default one can assume built automata are minimised before the
    * are returned.  Use this to enable or disable it
    */
  def setMinimize(minimize: Boolean): Unit = { this.minimize = minimize }

  /**
    * Create a fresh state that can be used in the automaton
    */
  def getNewState: BricsAutomaton#State = new BState()

  /**
    * Set the initial state
    */
  def setInitialState(q: BricsAutomaton#State): Unit =
    baut.setInitialState(q)

  /**
    * Add a new transition q1 --label--> q2
    */
  def addTransition(
      q1: BricsAutomaton#State,
      label: BricsAutomaton#TLabel,
      q2: BricsAutomaton#State
  ): Unit = {
    if (LabelOps.isNonEmptyLabel(label)) {
      val (min, max) = label
      q1.addTransition(new Transition(min, max, q2))
    }
  }

  // huzi add-----------------------------------------
  def addTransition(
      q1: BricsAutomaton#State,
      label: BricsAutomaton#TLabel,
      q2: BricsAutomaton#State,
      vector: List[Int]
  ): Unit = {
    if (LabelOps.isNonEmptyLabel(label)) {
      val (min, max) = label
      q1.addTransition(new Transition(min, max, q2))
      etaMap += ((q1, (min, max), q2) -> vector)
    }
  }

  def outgoingTransitions(
      q: BricsAutomaton#State
  ): Iterator[(BricsAutomaton#State, BricsAutomaton#TLabel)] =
    for (t <- q.getTransitions.iterator)
      yield (t.getDest, (t.getMin, t.getMax))

  def setAccept(q: BricsAutomaton#State, isAccepting: Boolean): Unit =
    q.setAccept(isAccepting)

  def isAccept(q: BricsAutomaton#State): Boolean = q.isAccept

  /**
    * Returns built automaton.  Can only be used once after which the
    * automaton cannot change
    */
  def getAutomaton: BricsAutomaton = {
    new BricsAutomaton(baut)
  }
}
