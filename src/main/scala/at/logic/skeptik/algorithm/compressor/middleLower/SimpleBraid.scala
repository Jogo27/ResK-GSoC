package at.logic.skeptik.algorithm.compressor.middleLower

//import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.E

import spire.algebra._   // provides algebraic type classes
import spire.math._      // provides functions, types, and type classes
import spire.implicits._ // provides infix operators, instances and conversions

import collection.immutable.{ HashMap => IMap }
import annotation.tailrec

object r {
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(node), ConflictGraph[GraphVertex](), IMap(), IMap())

  private[middleLower] abstract sealed class GraphVertex(val subproof: SequentProofNode) extends VertexAndOutgoingEdges[GraphVertex]
  private[middleLower] final case class SBThread(sp: SequentProofNode, val pivot: Either[E,E]) extends GraphVertex(sp) {
    require(pivot match {
      case Left(l)  => sp.conclusion.suc contains l
      case Right(l) => sp.conclusion.ant contains l
    })
    def edgeTo(other: GraphVertex) = pivot match {
      case Left(l)  => other.subproof.conclusion.ant contains l
      case Right(l) => other.subproof.conclusion.suc contains l
    }
    override def toString() =
//      hashCode().toString() + pivot.toString()
      subproof.conclusion.toString() + " " + pivot.toString()
  }
  private[middleLower] final case class SBMain(sp: SequentProofNode) extends GraphVertex(sp) with LeafWithoutOutgoingEdges[GraphVertex]
}
import r._

case class SimpleBraid(
  val main:    Option[SequentProofNode],
  val pGraph:  ConflictGraph[GraphVertex],
  val pending: Map[SBThread, Rational],
  val merged:  Map[SBThread, Rational]
) extends ProofBraid[SimpleBraid] {

  // Implentation of ProofBraid's interface

  def resolveWith(other: SimpleBraid, resolution: R):SimpleBraid = (this.sizes, other.sizes) match {

    // Less than 2 main threads
    case ((0,_,_), (0,_,_)) =>
      // TODO: check completed with Left(p) and corresponding Right(p)
      mergeMerged(other.merged).mergePending(other.pending)
    case ((1,_,_), (0,_,_)) =>
      mergeMerged(other.merged).mergePending(other.pending).mergeCompletePending()
    case ((0,_,_), (1,_,_)) =>
      other.mergeMerged(merged).mergePending(pending).mergeCompletePending()

    // Too simple cases
    case ((1,0,0), (1,0,0)) =>
      initBraid(R(main.get, other.main.get, resolution.auxL))

    case ((1,0,_), (1,0,_)) =>
      resolve(other.main.get, resolution.auxL).mergeMerged(other.merged).mergeCompletePending()

    // Regularisation cases
    case ((1,_,_), (1,_,_)) if (hasPending(Right(resolution.auxL))) && (other.main.get.conclusion contains resolution.auxL) =>
      println("** Resolution "+Right(resolution.auxL))
      mergeMerged(other.merged).mergePending(other.pending + (SBThread(other.main.get, Right(resolution.auxL)) -> Rational.one)) //TODO: Rational.zero
//      mergeMerged(other.pending).mergeMerged(other.merged).mergeCompletePending()
    case ((1,_,_), (1,_,_)) if (other.hasPending(Left(resolution.auxL))) && (main.get.conclusion contains resolution.auxL) =>
      println("** Resolution "+Left(resolution.auxL))
      other.mergeMerged(merged).mergePending(pending + (SBThread(main.get, Left(resolution.auxL)) -> Rational.one))
//      other.mergeMerged(pending).mergeMerged(merged).mergeCompletePending()

    // Delay cases
    case ((1,_,_), (1,_,_)) if !(main.get.conclusion.suc contains resolution.auxL) && (other.main.get.conclusion.ant contains resolution.auxL) =>
      println("** Delay case")
      mergePending(other.pending + (SBThread(other.main.get, Right(resolution.auxL)) -> Rational.one)).mergeMerged(other.merged).mergeCompletePending()
    case ((1,_,_), (1,_,_)) if (main.get.conclusion.suc contains resolution.auxL) && !(other.main.get.conclusion.ant contains resolution.auxL) =>
      println("** Delay case")
      other.mergePending(pending + (SBThread(main.get, Left(resolution.auxL)) -> Rational.one)).mergeMerged(merged).mergeCompletePending()


    // Main case
    case ((1,_,_), (1,_,_)) if (main.get.conclusion.suc contains resolution.auxL) && (other.main.get.conclusion.ant contains resolution.auxL) =>
      /* Recipe :
       * 1) Merge for the resolution
       * X) Merge if the other branch has already merge [Useless]
       * 3) Resolution
       * 5) Merge pending
       * 4) Merge merged
       */

      // Step 1
      val threadLeft  = prepareResolutionWith(SBThread(other.main.get, Right(resolution.auxL)))
      val threadRight = other.prepareResolutionWith(SBThread(main.get, Left(resolution.auxL)))

      // Step 3, 4 and 5
      threadLeft.resolve(threadRight.main.get, resolution.auxL).mergePending(threadRight.pending).mergeMerged(threadRight.merged).mergeCompletePending()


    // Hard cases: the pivot is neither on the left nor on the right
    case ((1,x,_), (1,y,_)) if (x*y > 0) && (main.get.conclusion.size <= other.main.get.conclusion.size) =>
      val finals = other.pending.keySet filter { _.subproof.conclusion.ant contains resolution.auxL }
      val braid = other.forceMerge(finals)
      val nPending = braid.pending + (SBThread(braid.main.get, Right(resolution.auxL)) -> Rational.one)
      mergeMerged(braid.merged).mergePending(nPending).mergeCompletePending()

    case ((1,x,_), (1,y,_)) if (x*y > 0) && (main.get.conclusion.size > other.main.get.conclusion.size) =>
      val finals = pending.keySet filter { _.subproof.conclusion.suc contains resolution.auxL }
      val braid = forceMerge(finals)
      val nPending = braid.pending + (SBThread(braid.main.get, Left(resolution.auxL)) -> Rational.one)
      other.mergeMerged(braid.merged).mergePending(nPending).mergeCompletePending()


    // Catch all
    case (t,o) => throw new Exception("Unhandled situation "+t+" "+o)
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
