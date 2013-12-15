package at.logic.skeptik.algorithm.compressor.middleLower

//import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.{E, EOrdering}

import spire.algebra._   // provides algebraic type classes
import spire.math._      // provides functions, types, and type classes
import spire.implicits._ // provides infix operators, instances and conversions

import collection.immutable.{ HashSet => ISet, HashMap => IMap, SortedMap => SortedMap, TreeMap => OMap }
import annotation.tailrec

object r2 {
  implicit def initBraid(node: SequentProofNode) = {
    val nMain = MainThread(node)
    StupidBraid(Some(nMain), OMap()(PendingThreadOrdering), ConflictGraph[StThread](nMain), OMap()(PendingThreadOrdering))
  }

  type Literal = Either[E,E]

  private[middleLower] abstract sealed class StThread(val subproof: SequentProofNode) extends VertexAndOutgoingEdges[StThread] {
    def conclusion = subproof.conclusion
    def hasLiteral(lit: Literal) = lit match {
      case Left(l)  => conclusion.ant contains l
      case Right(l) => conclusion.suc contains l
    }
    def resolvePivot(pivot: Literal) = pivot match  {
      case Right(l) => conclusion.ant contains l
      case Left(l)  => conclusion.suc contains l
    }
  }
  private[middleLower] final case class PendingThread(sp: SequentProofNode, val pivot: Either[E,E]) extends StThread(sp) {
    // TODO; It should be possible for a pending thread to not have its pivot in its conclusion. In such a case, the pivot
    //       has to be reintroduced by another pending from which this node is reachable in the graph.
    require(resolvePivot(pivot))

    def edgeTo(other: StThread) = other.hasLiteral(pivot)
    override def toString() =
  //      hashCode().toString() + pivot.toString()
      "PendingThread(" + subproof.conclusion.toString() + "," + pivot.toString() + ")"
  }
  private[middleLower] final case class MainThread(sp: SequentProofNode) extends StThread(sp) with LeafWithoutOutgoingEdges[StThread]

  object PendingThreadOrdering extends Ordering[PendingThread] {
    def compare(a: PendingThread, b: PendingThread) = (a.pivot, b.pivot) match {
      case (Left(_),  Right(_)) => -1
      case (Right(_), Left(_))  =>  1
      case (Left(x),  Left(y))  => EOrdering.compare(x,y)
      case (Right(x), Right(y)) => EOrdering.compare(x,y)
    }
  }
}
import r2._

case class StupidBraid(
  val main:      Option[MainThread],
  val actives:   SortedMap[PendingThread,Rational],
  val graph:     ConflictGraph[StThread],
  val inactives: SortedMap[PendingThread,Rational]
) extends ProofBraid[StupidBraid] {

  // DEBUG
  require(graph.nodes forall {
    case pending: PendingThread => actives contains pending
    case mainThread: MainThread => (!main.isEmpty) && (main.get eq mainThread)
  })

  // Implentation of ProofBraid's interface

  def resolveWith(other: StupidBraid, resolution: R):StupidBraid = (main.size, other.main.size) match {

//    case (0,_) =>
//      throw new NotImplementedError
//
//    case (_,0) =>
//      throw new NotImplementedError

    case _ =>
      val leftPivot = Right(resolution.auxL)
      val rightPivot = Left(resolution.auxL)
      println("Pivots "+leftPivot+" and "+rightPivot)
      val (leftStep1, withPivotLeft, shared, rightStep1, withPivotRight) = step1n2(other, leftPivot, rightPivot)
      println("Step1 " + leftStep1 + " and " + rightStep1)

      println("Sizes "+(this.actives.size, this.graph.size)+" and "+(other.actives.size, other.graph.size))
      println("Sizes "+(leftStep1.actives.size, leftStep1.graph.size)+" and "+(rightStep1.actives.size, rightStep1.graph.size))

      val (leftStep2,  leftDisconnected)  =
        if (leftStep1.main.isEmpty || shared.isEmpty)  (leftStep1,  ISet[PendingThread]()) else  leftStep1.removeDisconnectedPending()
      val (rightStep2, rightDisconnected) =
        if (rightStep1.main.isEmpty || shared.isEmpty) (rightStep1, ISet[PendingThread]()) else rightStep1.removeDisconnectedPending()
      println("Step2 " + leftStep2 + " and " + rightStep2)

      // Merge pending thread which have the pivot in their conclusion
      println("withPivotLeft "+withPivotLeft+"\nwithPivotRight "+withPivotRight)
      val mergePendingBefore = !(leftStep2.main.isEmpty || rightStep2.main.isEmpty)
      val leftStep3  =
        if (mergePendingBefore)
          (leftStep2  /: (withPivotLeft  -- leftDisconnected))  { _ mergeBranch _ }
        else
          leftStep2
      val rightStep3 =
        if (mergePendingBefore)
          (rightStep2 /: (withPivotRight -- rightDisconnected)) { _ mergeBranch _ }
        else
          rightStep2
      println("Step3 " + leftStep3 + " and " + rightStep3)

      // Construct the new graph (a draft)
      val (leftStep4, actives, graph, rightStep4) = leftStep3 mergeActiveBraid rightStep3
      println("Step4 " + leftStep4 + " and " + rightStep4)

      // Merge pending thread which have the pivot in their conclusion, if not done before
      def mergeAfter(acc: (StupidBraid, OMap[PendingThread, Rational], ConflictGraph[StThread]), pending: PendingThread) = {
        val (braid, actives, graph) = acc
        val removeIt = actives(pending) == braid.actives(pending)
        val nActives = if (removeIt) actives - pending else actives.updated(pending, actives(pending) - braid.actives(pending))
        (braid mergeBranch pending, nActives, if (removeIt) graph - pending else graph)
      }
      val mergePendingAfter = !(mergePendingBefore || leftStep4.main.isEmpty || rightStep4.main.isEmpty)
      val (leftStepB, activesA, graphA)  =
        if (mergePendingAfter)
          ((leftStep4, actives, graph)  /: (withPivotLeft  -- leftDisconnected)) (mergeAfter _)
        else
          (leftStep4, actives, graph)
      val (rightStepB, activesB, graphB) =
        if (mergePendingAfter)
          ((rightStep4 , activesA, graphA) /: (withPivotRight -- rightDisconnected)) (mergeAfter _)
        else
          (rightStep4, activesA, graphA)
      println("StepB " + leftStepB + " and " + rightStepB)

      val step6 =
        if (leftStepB.main.isEmpty) {
          println("Case left empty")
          val nGraph = if (rightStepB.main.isEmpty) graphB else (graphB + rightStepB.main.get)
          StupidBraid(rightStepB.main, activesB, nGraph, rightStepB.inactives).addInactives(leftStepB.inactives)
        }
        else if (rightStepB.main.isEmpty)
          StupidBraid(leftStepB.main, activesB, graphB + leftStepB.main.get, leftStepB.inactives).addInactives(rightStepB.inactives)
        else if (!leftStepB.main.get.hasLiteral(leftPivot))
            //TODO: check which alternative is faster
  //        val (step5, _) = StupidBraid(rightStepB.main, activesB, graphB + rightStepB.main.get, rightStepB.inactives).removeDisconnectedPending()
  //        step5.addInactives(leftStepB.inactives)
          rightStepB addConnectedFrom leftStepB
        else if (!rightStepB.main.get.hasLiteral(rightPivot))
          leftStepB addConnectedFrom rightStepB
        else {
          println("Main case")
          val nMain = MainThread(R(leftStepB.main.get.subproof, rightStepB.main.get.subproof, resolution.auxL))
          val step5 = StupidBraid(Some(nMain), activesB, graphB + nMain, OMap[PendingThread,Rational]()(PendingThreadOrdering))
          step5.addInactives(leftStepB.inactives).addInactives(rightStepB.inactives)
        }
      println("Step6 "+step6)

      val (stepC, disconnectedC) = step6.removeDisconnectedPending()
      if (!disconnectedC.isEmpty) {
        println("**** There was "+disconnectedC.size+" disconnected pendings before Step7 ****")
        for (pending <- disconnectedC) println("   * "+pending)
      }

      // TODO: When pending threads without their pivot would be allowed, care must be taken when merging complete pending.
      //       The right way to do it is probably to first extract the connected subgraph with only complete pendings,
      //       then when encountering a pending without its pivot:
      //        - if some incoming nodes (in the subgraph) have the pivot, merge their correponding branches into the pending
      //          without its pivot;
      //        - otherwise, don't merge it.
      def collectCompletedPending(p: StThread) = p match {
        case pending: PendingThread => stepC.actives(pending) == Rational.one
        case _ => false
      }
      val step7 = (stepC /: stepC.graph.collectReverseFrom(stepC.main, collectCompletedPending))
        { _ mergePending _.asInstanceOf[PendingThread] }

      // TODO: There should be no disconnected pending at that point
      val (step8, disconnected8) = StupidBraid(step7.main, step7.actives, step7.graph, step7.inactives filter { _._2 < Rational.one }).removeDisconnectedPending()
      if (!disconnected8.isEmpty) {
        println("**** There was "+disconnected8.size+" disconnected pendings ****")
        for (pending <- disconnected8) println("   * "+pending)
      }
      step8
  }
  
  def divise(divisor: Int, pivot: Literal):StupidBraid = {
    if (divisor == 1) this else {
      println("\nDivise "+this+" on "+pivot)
      val braid = mergeSubgraph(graph.transitiveSubgraph({ _.resolvePivot(pivot) }))
      lazy val nActives   = braid.actives   mapValues {_ / divisor}
      lazy val nInactives = braid.inactives mapValues {_ / divisor}
      braid.main match {
        case None =>
          StupidBraid(None, nActives, braid.graph, nInactives)

//        // TODO: remove that case and allow pending threads to not have their pivot in their conclusion
//        case Some(mainThread) if (!mainThread.resolvePivot(pivot)) =>
//          val subgraph =  graph.transitiveSubgraph({ _.resolvePivot(pivot) })
//          require(!subgraph.isEmpty)
//          mergeSubgraph(subgraph).divise(divisor, pivot)

        case Some(mainThread) =>
          require(mainThread.resolvePivot(pivot))
          var nThread = PendingThread(mainThread.subproof, pivot)
          val (in,out) = braid.graph.getInOut(nThread)
          // TODO: Instead of removing mainThread from out, handle tautologies correctly (puting everithing into inactives)
          val nBraid = (StupidBraid(Some(mainThread), nActives, braid.graph, nInactives) /: (out - mainThread)) {_ mergeBranch _.asInstanceOf[PendingThread]}
          println("braid "+nBraid)
          nThread = PendingThread(nBraid.main.get.subproof, pivot)
          StupidBraid(None, nBraid.actives + (nThread -> Rational.one / divisor), (nBraid.graph - nBraid.main.get) + nThread, nBraid.inactives)
      }
    }
  }

  def finalMerge = main match {
    case Some(mainThread) if (actives.size == 0) => mainThread.subproof

    // TODO: Case when actives is non-empty should never happen. It does because braid division is not done correctly.
    //       Division should be done whenever the braid has more than one child. Actives and inactives have to be divided by the number of children.
    //       Only the main thread has to be divided by the number of children with the same pivot (which might be one).
    //       See bug7.skeptik for a sample proof.
    case Some(mainThread) => mergeSubgraph(graph).main.get.subproof

    case _ => throw new Exception("Root node doesn't have all threads")
  }

  def effectiveConclusion = mergeSubgraph(graph).main.get.conclusion

  // New steps functions
  // TODO: rename them

  def step1n2(other: StupidBraid, leftPivot: Literal, rightPivot: Literal) = {
    // Step 1 and 2:
    // - replace duplicated pending with the same pivot
    // - compute shared pending (TODO: remove that)
    // - collect pending with resolution pivot

    val leftIt  =  this.actives.keys.iterator // TODO: Check if there is a better method to have an iteroator over a map's keys
    val rightIt = other.actives.keys.iterator

    def replacePending(fromBraid: StupidBraid, fromPending: PendingThread, toBraid: StupidBraid, toPending: PendingThread) = {
      val newPart = fromBraid.actives(fromPending) / 2
      val nFrom = StupidBraid(fromBraid.main, fromBraid.actives.updated(fromPending, newPart), fromBraid.graph, fromBraid.inactives)
      val nTo = StupidBraid(toBraid.main,
        (toBraid.actives - toPending) + (fromPending -> newPart), 
        (toBraid.graph - toPending) + fromPending,
        toBraid.inactives + (toPending -> toBraid.actives(toPending)) )
      (nFrom, nTo)
    }

    // TODO: Make single argument
    def checkPivot(pivot: Literal)(withPivot: ISet[PendingThread], pending: PendingThread) =
      if (pending.hasLiteral(pivot)) (withPivot + pending) else withPivot

    def oneSide(curPending: PendingThread, it: Iterator[PendingThread], pivot: Literal, withPivot: ISet[PendingThread]): ISet[PendingThread] = {
      println(" # One "+pivot+" start with "+withPivot)
//      (withPivot /: it)(checkPivot(pivot))
      def aux(cur: PendingThread, acc: ISet[PendingThread]): ISet[PendingThread] = {
        println("   --> "+cur)
        val nAcc = checkPivot(pivot)(acc, cur)
        if (it.hasNext) {
          aux(it.next, nAcc)
        }
        else
          nAcc
      }

      aux(curPending, withPivot)
    }

    def twoSides( curPendingLeft: PendingThread,  leftBraid: StupidBraid,  withPivotLeft: ISet[PendingThread],
                  shared: ISet[PendingThread],
                  curPendingRight: PendingThread, rightBraid: StupidBraid, withPivotRight: ISet[PendingThread]):
      (StupidBraid, ISet[PendingThread], ISet[PendingThread], StupidBraid, ISet[PendingThread]) =
      PendingThreadOrdering.compare(curPendingLeft, curPendingRight) match {
        case n if (n < 0) =>
          println(" # Neg "+withPivotLeft+" and "+withPivotRight+" => "+curPendingLeft)
          val nWithPivotLeft = checkPivot(leftPivot)(withPivotLeft, curPendingLeft)
          if (leftIt.hasNext)
            twoSides(leftIt.next, leftBraid, nWithPivotLeft, shared, curPendingRight, rightBraid, withPivotRight)
          else {
            val nWithPivotRight = oneSide(curPendingRight, rightIt, rightPivot, withPivotRight)
            (leftBraid, nWithPivotLeft, shared, rightBraid, nWithPivotRight)
          }
        case p if (p > 0) =>
          println(" # Pos "+withPivotLeft+" and "+withPivotRight+" => "+curPendingRight)
          val nWithPivotRight = checkPivot(rightPivot)(withPivotRight, curPendingRight)
          if (rightIt.hasNext)
            twoSides(curPendingLeft, leftBraid, withPivotLeft, shared, rightIt.next, rightBraid, nWithPivotRight)
          else {
            val nWithPivotLeft = oneSide(curPendingLeft, leftIt, leftPivot, withPivotLeft)
            println(" ## End neg with"+nWithPivotLeft)
            (leftBraid, nWithPivotLeft, shared, rightBraid, nWithPivotRight)
          }
        case 0 if (curPendingLeft.subproof eq curPendingRight.subproof) =>
          println(" # Sam "+withPivotLeft+" and "+withPivotRight)
          nextBoth(leftBraid, withPivotLeft, shared + curPendingLeft, rightBraid, withPivotRight)
        case 0 =>
          println(" # Dif "+withPivotLeft+" and "+withPivotRight)
          val leftBranch  =  leftBraid.graph.transitiveSubgraph({_ eq curPendingLeft})
          val rightBranch = rightBraid.graph.transitiveSubgraph({_ eq curPendingRight})
          val nWithPivotLeft  = checkPivot(leftPivot) (withPivotLeft,  curPendingLeft)
          val nWithPivotRight = checkPivot(rightPivot)(withPivotRight, curPendingRight)
          if (leftBranch.size < rightBranch.size)
            nextBoth(leftBraid mergeSubgraph leftBranch, nWithPivotLeft, shared, rightBraid, nWithPivotRight)
          else 
            nextBoth(leftBraid, nWithPivotLeft, shared, rightBraid mergeSubgraph rightBranch, nWithPivotRight)
//        case 0 => (curPendingLeft.hasLiteral(leftPivot), curPendingRight.hasLiteral(rightPivot)) match {
//          case (false, true) =>
//            val (nLeft, nRight) = replacePending(leftBraid, curPendingLeft, rightBraid, curPendingRight)
//            val withPivot = checkPivot(rightPivot)(withPivotRight, curPendingLeft)
//            nextBoth(nLeft, withPivotLeft, shared + curPendingLeft, nRight, withPivot)
//          case (true, false) =>
//            val (nRight, nLeft) = replacePending(rightBraid, curPendingRight, leftBraid, curPendingLeft)
//            val withPivot = checkPivot(leftPivot)(withPivotLeft, curPendingRight)
//            nextBoth(nLeft, withPivot, shared + curPendingRight, nRight, withPivotRight)
//          case (true,true) => //TODO: Don't really know what to do in that case. Some improvements may be possible.
//            nextBoth(leftBraid, withPivotLeft + curPendingLeft, shared, rightBraid, withPivotRight + curPendingRight)
//          case (false, false) if (curPendingLeft.conclusion.size < curPendingRight.conclusion.size) =>
//            val (nLeft, nRight) = replacePending(leftBraid, curPendingLeft, rightBraid, curPendingRight)
//            val withPivot = checkPivot(rightPivot)(withPivotRight, curPendingLeft)
//            nextBoth(nLeft, withPivotLeft, shared + curPendingLeft, nRight, withPivot)
//          case _ =>
//            val (nRight, nLeft) = replacePending(rightBraid, curPendingRight, leftBraid, curPendingLeft)
//            val withPivot = checkPivot(leftPivot)(withPivotLeft, curPendingRight)
//            nextBoth(nLeft, withPivot, shared + curPendingRight, nRight, withPivotRight)
//        }
      }
          
    def nextBoth( leftBraid: StupidBraid, withPivotLeft: ISet[PendingThread],
                  shared: ISet[PendingThread],
                  rightBraid: StupidBraid, withPivotRight: ISet[PendingThread]) =
      (leftIt.hasNext, rightIt.hasNext) match {
        case (false, false) => (leftBraid, withPivotLeft, shared, rightBraid, withPivotRight)
        case (false, true) =>
            val withPivot = oneSide(rightIt.next, rightIt, rightPivot, withPivotRight)
            (leftBraid, withPivotLeft, shared, rightBraid, withPivot)
        case (true, false) =>
            val withPivot = oneSide(leftIt.next, leftIt, leftPivot, withPivotLeft)
            (leftBraid, withPivot, shared, rightBraid, withPivotRight)
        case (true, true) =>
            twoSides(leftIt.next, leftBraid, withPivotLeft, shared, rightIt.next, rightBraid, withPivotRight)
      }

    val emptySet = ISet[PendingThread]()
    nextBoth(this, emptySet, emptySet, other, emptySet)
  }

  def mergeActiveBraid(other: StupidBraid) = {
    //PRECONDITIONS: both graphs have to be connected because of the call to reverseOrder

    //DEBUG
    if (!main.isEmpty)
      println("Disconnected self "+graph.disconnectedFrom(main.get))
    if (!other.main.isEmpty)
      println("Disconnected other "+other.graph.disconnectedFrom(other.main.get))

    def aux(leftIt: Iterator[StThread], leftBraid: StupidBraid, rightIt: Iterator[StThread], rightBraid: StupidBraid,
            leftIsLeft: Boolean, actives: OMap[PendingThread,Rational], graph: CycleDetectorGraph[StThread]):
            (StupidBraid, OMap[PendingThread,Rational], ConflictGraph[StThread], StupidBraid) =
      if (leftIt.hasNext) 
        leftIt.next match {
          case next: PendingThread =>
            println("  add " + next + " to " + leftBraid + " left " + leftIsLeft)
            if (actives contains next) {
              val nActives = actives.updated(next, actives(next) + leftBraid.actives(next))
              aux(rightIt, rightBraid, leftIt, leftBraid, !leftIsLeft, nActives, graph)
            }
            else graph.addIfNoCycle(next) match {
              case None =>
                aux(rightIt, rightBraid, leftIt, leftBraid.mergeBranch(next), !leftIsLeft, actives, graph)
              case Some(nGraph) =>
                val nActives = actives + (next -> leftBraid.actives(next))
                aux(rightIt, rightBraid, leftIt, leftBraid, !leftIsLeft, nActives, nGraph)
            }
          case _ =>
            println("  main " + leftBraid + " left " + leftIsLeft)
            aux(leftIt, leftBraid, rightIt, rightBraid, leftIsLeft, actives, graph)
        }
      else if (rightIt.hasNext) {
        println("  reverse " + leftBraid + " left " + leftIsLeft)
        aux(rightIt, rightBraid, leftIt, leftBraid, !leftIsLeft, actives, graph)
      }
      else {
        if (leftIsLeft)
          (leftBraid, actives, graph.toConflictGraph, rightBraid)
        else
          (rightBraid, actives, graph.toConflictGraph, leftBraid)
      }

    aux(graph.reverseOrder, this, other.graph.reverseOrder, other,
        true, OMap[PendingThread,Rational]()(PendingThreadOrdering), CycleDetectorGraph[StThread]())
  }

  def addConnectedFrom(other: StupidBraid) = { //Subsumption
    println("Case subsumption")
    // Actives
    val braidWithActive = (this /: other.graph.reverseOrder) { (braid, p) => p match {
      case pending: PendingThread =>
        val pending = p.asInstanceOf[PendingThread]
        if (braid.actives contains pending) {
          val nActives =  braid.actives.updated(pending, braid.actives(pending) + other.actives(pending))
          StupidBraid(braid.main, nActives, braid.graph, braid.inactives)
        }
        else if (braid.inactives contains pending) {
          val nInactives =  braid.inactives.updated(pending, braid.inactives(pending) + other.actives(pending))
          StupidBraid(braid.main, braid.actives, braid.graph, nInactives)
        }
        else {
          val (in,out) = braid.graph.getInOut(pending)
          if (out.isEmpty) {
            val nInactives = braid.inactives + (pending -> other.actives(pending))
            StupidBraid(braid.main, braid.actives, braid.graph, nInactives)
          }
          else {
            val nActives =  braid.actives + (pending -> other.actives(pending))
            val nGraph = braid.graph.add(pending, in, out)
            StupidBraid(braid.main, nActives, nGraph, braid.inactives)
          }
        }
      case _ => braid
    }}
    // Inactives
    (braidWithActive /: other.inactives.keys) { (braid, pending) =>
      if (braid.actives contains pending) {
        val nActives =  braid.actives.updated(pending, braid.actives(pending) + other.inactives(pending))
        StupidBraid(braid.main, nActives, braid.graph, braid.inactives)
      }
      else {
        val nInactives =  braid.inactives.updated(pending, braid.inactives.getOrElse(pending, Rational.zero) + other.inactives(pending))
        StupidBraid(braid.main, braid.actives, braid.graph, nInactives)
      }
    } 
  }




  // pending methods

  def mergePending(thread: PendingThread) = {
    println("Merging "+thread.conclusion+" into "+(main map {_.conclusion}).toString()+" on "+thread.pivot)
    val fraction = actives(thread)
    val subproof = thread.subproof
    val (nMain, nGraph: ConflictGraph[StThread]) = (main, thread.pivot) match {
      case (None, _)           => (Some(MainThread(subproof)), graph)
      case (Some(m), Left(p))  => (Some(MainThread(R(subproof, m.subproof, p))), graph - m)
      case (Some(m), Right(p)) => (Some(MainThread(R(m.subproof, subproof, p))), graph - m)
    }
    StupidBraid(nMain, actives - thread, (nGraph - thread) + nMain.get, if (fraction < Rational.one) inactives + (thread -> fraction) else inactives)
  }

  def mergeBranch(thread: PendingThread) =
    // TODO: optimize
    mergeSubgraph(graph.transitiveSubgraph({_ == thread}))

  def mergeSubgraph(subgraph: ConflictGraph[StThread]) =
    (this /: subgraph.reverseOrder) {
      case (braid, pending: PendingThread) => braid mergePending pending
      case (braid, _) => braid
    }

  def removeDisconnectedPending() = main match {
    case None => (this, ISet[PendingThread]())
    case Some(mainThread) =>
      val disconnected = graph.disconnectedFrom(mainThread) map {
        case p : PendingThread => p
      }
      val nInactives = (inactives /: disconnected) { (acc, pending) => acc + (pending -> actives(pending)) }
      (StupidBraid(main, actives -- disconnected, graph -- disconnected, nInactives), disconnected)
  }

  def addInactives(m: Map[PendingThread, Rational]) = (this /: m) { (braid, kv) =>
    val (pending, fraction) = kv
    if (braid.actives contains pending) {
      val nPart = fraction + braid.actives(pending)
      StupidBraid(braid.main, braid.actives + (pending -> nPart), braid.graph, braid.inactives)
    }
    else if (braid.inactives contains pending) {
      val nPart = fraction + braid.inactives(pending)
      if (nPart < Rational.one) 
        StupidBraid(braid.main, braid.actives, braid.graph, braid.inactives + (pending -> nPart))
      else
        StupidBraid(braid.main, braid.actives, braid.graph, braid.inactives - pending)
    }
    else
      StupidBraid(braid.main, braid.actives, braid.graph, braid.inactives + (pending -> fraction))
  }

}

object StupidMiddleLower extends MiddleLower[StupidBraid]
