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
  }
  private[middleLower] final case class PendingThread(sp: SequentProofNode, val pivot: Either[E,E]) extends StThread(sp) {
    require(pivot match {
      case Left(l)  => sp.conclusion.suc contains l
      case Right(l) => sp.conclusion.ant contains l
    })
    def edgeTo(other: StThread) = pivot match {
      case Left(l)  => other.conclusion.ant contains l
      case Right(l) => other.conclusion.suc contains l
    }
    override def toString() =
  //      hashCode().toString() + pivot.toString()
      subproof.conclusion.toString() + " " + pivot.toString()
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

  // Implentation of ProofBraid's interface

  def resolveWith(other: StupidBraid, resolution: R):StupidBraid = (main.size, other.main.size) match {

    case (0,_) =>
      throw new NotImplementedError

    case (_,0) =>
      throw new NotImplementedError

    case _ =>
      val leftPivot = Right(resolution.auxL)
      val rightPivot = Left(resolution.auxL)
      val (leftStep1, withPivotLeft, shared, rightStep1, withPivotRight) = step1n2(other, leftPivot, rightPivot)

      // TODO: don't check for disconnected if nothing is shared
      val (leftStep2,  leftDisconnected)  =  leftStep1.removeDisconnectedPending()
      val (rightStep2, rightDisconnected) = rightStep1.removeDisconnectedPending()

      // Merge pending thread which have the pivot in their conclusion
      val leftStep3  = (leftStep2  /: (withPivotLeft  -- leftDisconnected))  { _ mergeBranch _ }
      val rightStep3 = (rightStep2 /: (withPivotRight -- rightDisconnected)) { _ mergeBranch _ }

      // Construct the new graph (a draft)
      val (leftStep4, actives, graph, rightStep4) = leftStep3 mergeActiveBraid rightStep3

      val step6 =
        if (!leftStep4.main.get.hasLiteral(leftPivot))
            //TODO: check which alternative is faster
  //        val (step5, _) = StupidBraid(rightStep4.main, actives, graph + rightStep4.main.get, rightStep4.inactives).removeDisconnectedPending()
  //        step5.addInactives(leftStep4.inactives)
          rightStep4 addConnectedFrom leftStep4
        else if (!rightStep4.main.get.hasLiteral(rightPivot))
          leftStep4 addConnectedFrom rightStep4
        else {
          val nMain = MainThread(R(leftStep4.main.get.subproof, rightStep4.main.get.subproof, resolution.auxL))
          val step5 = StupidBraid(Some(nMain), actives, graph + nMain, OMap[PendingThread,Rational]()(PendingThreadOrdering))
          step5.addInactives(leftStep4.inactives).addInactives(rightStep4.inactives)
        }

      val step7 = (step6 /: step6.graph.collectReverseFrom(step6.main.get, {p => step6.actives(p.asInstanceOf[PendingThread]) == Rational.one}))
        { _ mergePending _.asInstanceOf[PendingThread] }
      StupidBraid(step7.main, step7.actives, step7.graph, step7.inactives filter { _._2 < Rational.one })
  }
  
  def divise(divisor: Int, pivot: Literal) = {
    if (divisor == 1) this else {
//      println("\nDivise "+this+" on "+pivot)
      lazy val nActives   =  actives  mapValues {_ / divisor}
      lazy val nInactives = inactives mapValues {_ / divisor}
      main match {
        case None =>
          StupidBraid(None, nActives, graph, nInactives)
        case Some(mainThread) =>
          var nThread = PendingThread(mainThread.subproof, pivot)
          val (in,out) = graph.getInOut(nThread)
          val braid = (StupidBraid(Some(mainThread), nActives, graph, nInactives) /: out) {_ mergeBranch _.asInstanceOf[PendingThread]} //TODO don't work for tautologies
          println("braid "+braid)
          nThread = PendingThread(braid.main.get.subproof, pivot)
          StupidBraid(None, braid.actives + (nThread -> Rational.one / divisor), (graph - braid.main.get) + nThread, braid.inactives)
      }
    }
  }

  def finalMerge = main match {
    case Some(mainThread) => mainThread.subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }

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

    def checkPivot(pivot: Literal)(withPivot: ISet[PendingThread], pending: PendingThread) =
      if (pending.hasLiteral(pivot)) (withPivot + pending) else withPivot

    def oneSide(it: Iterator[PendingThread], pivot: Literal, withPivot: ISet[PendingThread]): ISet[PendingThread] =
      (withPivot /: it)(checkPivot(pivot))

    def twoSides( curPendingLeft: PendingThread,  leftBraid: StupidBraid,  withPivotLeft: ISet[PendingThread],
                  shared: ISet[PendingThread],
                  curPendingRight: PendingThread, rightBraid: StupidBraid, withPivotRight: ISet[PendingThread]):
      (StupidBraid, ISet[PendingThread], ISet[PendingThread], StupidBraid, ISet[PendingThread]) =
      PendingThreadOrdering.compare(curPendingLeft, curPendingRight) match {
        case n if (n < 0) =>
          if (leftIt.hasNext) {
            val withPivot = checkPivot(leftPivot)(withPivotLeft, curPendingLeft)
            twoSides(leftIt.next, leftBraid, withPivot, shared, curPendingRight, rightBraid, withPivotRight)
          }
          else {
            val withPivot = oneSide(rightIt, rightPivot, withPivotRight)
            (leftBraid, withPivotLeft, shared, rightBraid, withPivot)
          }
        case p if (p > 0) =>
          if (rightIt.hasNext) {
            val withPivot = checkPivot(rightPivot)(withPivotRight, curPendingRight)
            twoSides(curPendingLeft, leftBraid, withPivotLeft, shared, rightIt.next, rightBraid, withPivot)
          }
          else {
            val withPivot = oneSide(leftIt, leftPivot, withPivotLeft)
            (leftBraid, withPivot, shared, rightBraid, withPivotRight)
          }
        case 0 => (curPendingLeft.hasLiteral(leftPivot), curPendingRight.hasLiteral(rightPivot)) match {
          case (false, true) =>
            val (nLeft, nRight) = replacePending(leftBraid, curPendingLeft, rightBraid, curPendingRight)
            val withPivot = checkPivot(rightPivot)(withPivotRight, curPendingLeft)
            nextBoth(nLeft, withPivotLeft, shared + curPendingLeft, nRight, withPivot)
          case (true, false) =>
            val (nRight, nLeft) = replacePending(rightBraid, curPendingRight, leftBraid, curPendingLeft)
            val withPivot = checkPivot(leftPivot)(withPivotLeft, curPendingRight)
            nextBoth(nLeft, withPivot, shared + curPendingRight, nRight, withPivotRight)
          case (true,true) => //TODO: Don't really know what to do in that case. Some improvements may be possible.
            nextBoth(leftBraid, withPivotLeft + curPendingLeft, shared, rightBraid, withPivotRight + curPendingRight)
          case (false, false) if (curPendingLeft.conclusion.size < curPendingRight.conclusion.size) =>
            val (nLeft, nRight) = replacePending(leftBraid, curPendingLeft, rightBraid, curPendingRight)
            val withPivot = checkPivot(rightPivot)(withPivotRight, curPendingLeft)
            nextBoth(nLeft, withPivotLeft, shared + curPendingLeft, nRight, withPivot)
          case _ =>
            val (nRight, nLeft) = replacePending(rightBraid, curPendingRight, leftBraid, curPendingLeft)
            val withPivot = checkPivot(leftPivot)(withPivotLeft, curPendingRight)
            nextBoth(nLeft, withPivot, shared + curPendingRight, nRight, withPivotRight)
        }
      }
          
    def nextBoth( leftBraid: StupidBraid, withPivotLeft: ISet[PendingThread],
                  shared: ISet[PendingThread],
                  rightBraid: StupidBraid, withPivotRight: ISet[PendingThread]) =
      (leftIt.hasNext, rightIt.hasNext) match {
        case (false, false) => (leftBraid, withPivotLeft, shared, rightBraid, withPivotRight)
        case (false, true) =>
            val withPivot = oneSide(rightIt, rightPivot, withPivotRight)
            (leftBraid, withPivotLeft, shared, rightBraid, withPivot)
        case (true, false) =>
            val withPivot = oneSide(leftIt, leftPivot, withPivotLeft)
            (leftBraid, withPivot, shared, rightBraid, withPivotRight)
        case (true, true) =>
            twoSides(leftIt.next, leftBraid, withPivotLeft, shared, rightIt.next, rightBraid, withPivotRight)
      }

    val emptySet = ISet[PendingThread]()
    nextBoth(this, emptySet, emptySet, other, emptySet)
  }

  def mergeActiveBraid(other: StupidBraid) = {
    def aux(leftIt: Iterator[StThread], leftBraid: StupidBraid, rightIt: Iterator[StThread], rightBraid: StupidBraid,
            leftIsLeft: Boolean, actives: OMap[PendingThread,Rational], graph: CycleDetectorGraph[StThread]):
            (StupidBraid, OMap[PendingThread,Rational], ConflictGraph[StThread], StupidBraid) =
      if (leftIt.hasNext) {
        val next = leftIt.next.asInstanceOf[PendingThread]
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
      }
      else if (rightIt.hasNext) {
        aux(rightIt, rightBraid, leftIt, rightBraid, !leftIsLeft, actives, graph)
      }
      else {
        if (leftIsLeft)
          (leftBraid, actives, graph.toConflictGraph, rightBraid)
        else
          (rightBraid, actives, graph.toConflictGraph, leftBraid)
      }

    //TODO: It's assumed here that main in not None
    aux(graph.reverseOrderFrom(main.get), this, other.graph.reverseOrderFrom(other.main.get), other,
        true, OMap[PendingThread,Rational]()(PendingThreadOrdering), CycleDetectorGraph[StThread]())
  }

  def addConnectedFrom(other: StupidBraid) = { //Subsumption
    // Actives
    val braidWithActive = (this /: other.graph.reverseOrder) { (braid, p) =>
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
    }
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
//    println("Merging "+subproof.conclusion+" into "+(main map {_.conclusion}).toString()+" on "+pivot)
    val fraction = actives(thread)
    val subproof = thread.subproof
    val nMain = (main, thread.pivot) match {
      case (None, _)           => Some(MainThread(subproof))
      case (Some(m), Left(p))  => Some(MainThread(R(subproof, m.subproof, p)))
      case (Some(m), Right(p)) => Some(MainThread(R(m.subproof, subproof, p)))
    }
    StupidBraid(nMain, actives - thread, graph - thread, if (fraction < Rational.one) inactives + (thread -> fraction) else inactives)
  }

  def mergeBranch(thread: PendingThread) =
    // TODO: optimize
    (this /: graph.transitiveSubgraph({_ eq thread}).reverseOrder) {
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
