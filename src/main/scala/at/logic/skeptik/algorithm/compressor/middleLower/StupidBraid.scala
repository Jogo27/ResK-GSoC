package at.logic.skeptik.algorithm.compressor.middleLower

//import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.E

import spire.algebra._   // provides algebraic type classes
import spire.math._      // provides functions, types, and type classes
import spire.implicits._ // provides infix operators, instances and conversions

import collection.immutable.{ HashMap => IMap, TreeMap => OMap }
import annotation.tailrec

object r {
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(node), ConflictGraph[GraphVertex](), IMap(), IMap())

  type Literal = Either[E,E]

  private[middleLower] abstract sealed class StThread(val subproof: SequentProofNode) extends VertexAndOutgoingEdges[GraphVertex] {
    def conclusion = subproof.conclusion
  }
  private[middleLower] final case class PendingThread(sp: SequentProofNode, val pivot: Either[E,E]) extends GraphVertex(sp) {
    require(pivot match {
      case Left(l)  => sp.conclusion.suc contains l
      case Right(l) => sp.conclusion.ant contains l
    })
    def edgeTo(other: GraphVertex) = pivot match {
      case Left(l)  => other.conclusion.ant contains l
      case Right(l) => other.conclusion.suc contains l
    }
    override def toString() =
  //      hashCode().toString() + pivot.toString()
      subproof.conclusion.toString() + " " + pivot.toString()
  }
  private[middleLower] final case class MainThread(sp: SequentProofNode) extends GraphVertex(sp) with LeafWithoutOutgoingEdges[GraphVertex]

  object PendingThreadOrdering extends Ordering[PendingThread] {
    def compare(a: PendingThread, b: PendingThread) = (a.pivot, b.pivot) match {
      case (Left(_),  Right(_)) => -1
      case (Right(_), Left(_))  =>  1
      case (Left(x),  Left(y))  => x compare y
      case (Right(x), Right(y)) => x compare y
    }
  }
}
import r._

case class StupidBraid(
  val main:      Option[SequentProofNode],
  val actives:   OMap[PendingThread,Rational],
  val graph:     Graph[StThread],
  val inactives: OMap[PendingThread,Rational]
) extends ProofBraid[StupidBraid] {

  // Implentation of ProofBraid's interface

  def resolveWith(other: StupidBraid, resolution: R):StupidBraid = (main.sizes, other.main.sizes) match {

    case (0,_) =>
      throw new NotImplementedError

    case (_,0) =>
      throw new NotImplementedError

    case _ =>
      // Step 1 and 2:
      // - replace duplicated pending with the same pivot
      // - compute shared pending
      // - collect pending with resolution pivot

      def step1n2(leftIt: Iterator[PendingThread], rightIt: Iterator[PendingThread]) = {

        def checkPivot(pivot: Literal)(withPivot: ISet[PendingThread], pending: PendingThread) =
          if (pending.hasLiteral(pivot)) (withPivot + pending) else withPivot

        def oneSide(it: Iterator[PendingThread], pivot: Literal, withPivot: ISet[PendingThread]): ISet[PendingThread] =
          (withPivot :/ it) checkPivot(pivot)

        def twoSides( curPendingLeft: PendingThread,  leftBraid: StupidBraid,  withPivotLeft: ISet[PendingThread],
                      shared: ISet[PendingThread],
                      curPendingRight: PendingThread, rightBraid: StupidBraid, withPivotRight: ISet[PendingThread]):
          (StupidBraid, ISet[PendingThread], ISet[PendingThread], StupidBraid, ISet[PendingThread]) =
          PendingThreadOrdering.compare(curPendingLeft, curPendingRight) match {
            case n if (n < 0) =>
              if (leftIt.hasNext()) {
                val withPivot = checkPivot(leftPivot)(withPivotLeft, curPendingLeft)
                twoSides(leftIt.next, leftBraid, withPivot, shared, curPendingRight, rightBraid, withPivotRight)
              }
              else {
                val withPivot = oneSide(rightIt, rightPivot, withPivotRight)
                (leftBraid, withPivotLeft, shared, rightBraid, withPivot)
              }
            case p if (p > 0) =>
              if (rightIt.hasNext()) {
                val withPivot = checkPivot(rightPivot)(withPivotRight, curPendingRight)
                twoSides(curPendingLeft, leftBraid, withPivotLeft, shared, rightIt.next, rightBraid, withPivot)
              }
              else {
                val withPivot = oneSide(leftIt, leftPivot, withPivotLeft)
                (leftBraid, withPivot, shared, rightBraid, withPivotRight)
              }
            case 0 => (curPendingLeft.hasLiteral(leftPivot), curPendingRight.hasLiteral(rightPivot)) match {
              case (false, true) =>
                val newPart = leftBraid.actives(curPendingLeft) / 2
                val nLeft = StupidBraid(leftBraid.main, leftBraid.actives.updated(curPendingLeft, newPart), leftBraid.graph, leftBraid.inactives)
                val nRight = StupidBraid(rightBraid.main, // TODO
              
          }
      

  }
  
  def divise(divisor: Int, pivot: Either[E,E]) = {
//    require((if (main.isEmpty) pGraph else pGraph + SBMain(main.get)).leaves.size == 1, this)
    if (divisor == 1) this else {
      println("\nDivise "+this+" on "+pivot)
//      pGraph.aff()
      val subproofFilter = pivot match {
        case Left(l)  => { s:SequentProofNode => s.conclusion.suc contains l }
        case Right(l) => { s:SequentProofNode => s.conclusion.ant contains l }
      }

      lazy val pendingDivided = pending mapValues {_ / divisor}
      lazy val mergedDivided  = merged  mapValues {_ / divisor}
      main match {
        case None =>
          SimpleBraid(None, pGraph, pendingDivided, mergedDivided)
        case Some(subproof) if subproofFilter(subproof) =>
          val nThread = SBThread(subproof, pivot)
          SimpleBraid(None, pGraph + nThread, pendingDivided + (nThread -> (Rational.one / divisor)), mergedDivided)
        case Some(subproof) if hasPending(pivot) =>
          throw new NotImplementedError("TODO: Allow SBMain in pending")
//          val nThread = SBMain(subproof)
//          SimpleBraid(None, pGraph + nThread, pendingDivided + (nThread -> (Rational.one / divisor)), mergedDivided)
        case Some(subproof) =>
          val finals = pending.keySet filter { v:GraphVertex => subproofFilter(v.subproof) }
          val braid = forceMerge(finals)
          println("braid "+braid)
          val nThread = SBThread(braid.main.get, pivot)
          SimpleBraid(None, braid.pGraph + nThread, pendingDivided + (nThread -> (Rational.one / divisor)), mergedDivided)
      }
    }
  }

  def finalMerge = main match {
    case Some(subproof) => println("Final "+sizes) ; pGraph.aff() ; subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }


  // Utils functions

  def prepareResolutionWith(other: SBThread) = {
    val (_,out) = pGraph.getInOut(other)
    val subgraph = pGraph.transitiveSubgraph(out)
    (this /: subgraph.reverseOrderFrom(SBMain(main.get))) { _ merge _ }
  }

  // main methods

  def resolve(subproof: SequentProofNode, pivot: E) = 
    SimpleBraid(Some(R(main.get, subproof, pivot)), pGraph, pending, merged)

  // pending methods

  def hasPending(pivot: Either[E,E]) = pending exists { kv =>
    val (SBThread(_,other),_) = kv
    other == pivot
  }

  def merge(v: GraphVertex) = v match {
    case thread @ SBThread(subproof, pivot) =>
      println("Merging "+subproof.conclusion+" into "+(main map {_.conclusion}).toString()+" on "+pivot)
      val fraction = pending(thread)
      val nMerged = if (fraction < Rational.one) merged + (thread -> fraction) else merged
      (main, pivot) match {
        case (None, _)           => SimpleBraid(Some(subproof),          pGraph - thread, pending - thread, nMerged)
        case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pGraph - thread, pending - thread, nMerged)
        case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pGraph - thread, pending - thread, nMerged)
      }
    case _ => throw new Exception("Unable to merge non-thread")
  }

  def forceMerge(f: Set[SBThread]) = main match {
    case None => throw new NotImplementedError()
    case Some(subproof) =>
          /* Recipe if subproof doesn't contain the pivot:
           * 1) add SBMain to the graph
           * 2) collect finals threads (ie having the pivots)
           * 3) extract the transitive subgraph
           * 4) remove finals in cycles as long as they're still some finals left
           * 5) if there are still cycles involving finals, removes the edges going to an arbitrary selected final
           * 6) topological sort and merge
           */

          // Step 1
          // TODO because it's useless until the previous case happens
  
      val finals = f map { _.asInstanceOf[GraphVertex] }
      println("Finals "+finals.size)
      for (v <- finals) { println("  "+v.subproof.conclusion) }


      // Remove Cycles
      @tailrec
      def removeCycles(graph: ConflictGraph[GraphVertex], finals: Set[GraphVertex]):ConflictGraph[GraphVertex] = {
        val subgraph = graph transitiveSubgraph finals
        subgraph.findCycle match {
          case None => subgraph
          case Some(cycle) if (cycle & finals).isEmpty =>
            println("Found non-finals cycle")
            
            if (cycle.size == 2) {
              val (first:SBThread)::(second:SBThread)::Nil = cycle.toList
              println("  "+first+" <-> "+second)
              removeCycles(subgraph.removeCycle(cycle), finals)
//              removeCycles(((subgraph - first) - second) + SBMain(R(first.subproof, second.subproof)), finals)
//              val subfirst = subgraph.removeEdge(first, second)
//              if (subfirst.hasPath(first,second))
//                removeCycles(subgraph.removeEdge(second, first), finals)
//              else
//                removeCycles(subfirst, finals)
            }
            else
              cycle find {
                case ta @ SBThread(_,pa) => subgraph exists {
                    case tb @ SBThread(_,pb) => pa == pb && !cycle(tb)
                    case _ => false
                  }
                case _ => false
              } match {
                case Some(v) =>
                  println("Removing edges from "+v)
                  removeCycles(subgraph.removeEdges(v, cycle), finals)
                case None =>
                  removeCycles(subgraph.removeCycle(cycle), finals)
              }
          case Some(cycle) =>
            println("Found finals cycle "+cycle)
            val nFinals = finals &~ cycle
            if (nFinals.isEmpty)
              removeCycles(subgraph.removeIncomingTo(cycle.head), finals)
            else
              removeCycles(subgraph, nFinals)
        }
      }

      val subgraph = removeCycles(pGraph.removeIncomingsTo(finals) + SBMain(subproof), finals).removeLeavesBut(SBMain(subproof))
      println("cycles removed ("+subgraph.size+"):")
      subgraph.aff()

      // Step 5bis: ensure each node has at most one incoming edge labeled with any pivot
      val (step5bisSubgraph, _) = ((subgraph, IMap[Either[E,E],Set[GraphVertex]]()) /: subgraph.sortByIncoming) { (acc,v) =>
        val (subgraph, pivots) = acc
        println("5bis "+v+" with "+pivots)
        v match {
          case SBThread(_,pivot) if pivots contains pivot =>
            val curTo = pivots(pivot)
            println("Removing from "+v+" to "+(curTo & subgraph.outgoings(v)))
            (subgraph.removeEdges(v, curTo), pivots + (pivot -> (curTo ++ subgraph.outgoings(v))))
          case SBThread(_,pivot) =>
            (subgraph, pivots + (pivot -> subgraph.outgoings(v)))
          case _ =>
            (subgraph, pivots)
        }
      }
      val finalSubgraph = step5bisSubgraph.removeLeavesBut(SBMain(subproof))
      println("final ("+finalSubgraph.size+"):")
      finalSubgraph.aff()

      // Step 6
      (this /: finalSubgraph.reverseOrder) { _ merge _ }
    }

  def mergePending(m: Map[SBThread, Rational]) = (this /: m) { (acc,kv) =>
    val (key, fraction) = kv
    if (acc.merged contains key) {
      val nfrac = fraction + acc.merged(key)
      SimpleBraid(acc.main, acc.pGraph + key, acc.pending + (key -> nfrac), acc.merged - key)
    }
    else if (acc.pending contains key) {
      val nfrac = fraction + acc.pending(key)
      SimpleBraid(acc.main, acc.pGraph, acc.pending + (key -> nfrac), acc.merged)
    }
    else
      SimpleBraid(acc.main, acc.pGraph + key, acc.pending + (key -> fraction), acc.merged)
  }

  def mergeCompletePending() = {
    // TODO: search for completed SBMain ?
    println("mergeCompletePending")
    pGraph.aff()
    val subgraph = pGraph.subgraph( {
      case key: SBThread => pending(key) >= Rational.one
      case x => false
    } )
    println("filtered ("+subgraph.size+"):")
    subgraph.aff()
    (this /: subgraph.reverseOrderFrom(SBMain(main.get))) { _ merge _ }
  }

  // merged methods

  def mergeMerged(m: Map[SBThread, Rational]) = (this /: m) { (acc,kv) =>
    val (key, fraction) = kv
    if (acc.pending contains key) {
      val nfrac = fraction + acc.pending(key)
      SimpleBraid(acc.main, acc.pGraph, acc.pending + (key -> nfrac), acc.merged)
    }
    else if (acc.merged contains key) {
      val nfrac = fraction + acc.merged(key)
      if (nfrac < Rational.one) 
        SimpleBraid(acc.main, acc.pGraph, acc.pending, acc.merged + (key -> nfrac))
      else
        SimpleBraid(acc.main, acc.pGraph, acc.pending, acc.merged - key)
    }
    else
      SimpleBraid(acc.main, acc.pGraph, acc.pending, acc.merged + (key -> fraction))
  }

  // Miscellaneous

  def sizes = (main.size, pending.size, merged.size)

  override def toString() =
    "(" +
    (main map { _.conclusion }).toString() + "," +
    pGraph.size + "," +
    (pending.keys map { _.pivot }).toString() + "," +
    (merged.keys map { _.pivot }).toString() + ")"

}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
