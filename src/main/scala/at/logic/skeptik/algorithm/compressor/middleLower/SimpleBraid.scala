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
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(node), IMap(), IMap())

  private[middleLower] abstract sealed class GraphVertex(val subproof: SequentProofNode) extends VertexAndOutgoingEdges[GraphVertex]
  private[middleLower] final case class SBThread(sp: SequentProofNode, val pivot: Either[E,E]) extends GraphVertex(sp) {
    def edgeTo(other: GraphVertex) = pivot match {
      case Left(l)  => other.subproof.conclusion.ant contains l
      case Right(l) => other.subproof.conclusion.suc contains l
    }
  }
  private[middleLower] final case class SBMain(sp: SequentProofNode) extends GraphVertex(sp) with LeafWithoutOutgoingEdges[GraphVertex]
}
import r._

case class SimpleBraid(
  val main:    Option[SequentProofNode],
  val pending: Map[SBThread, Rational],
  val merged:  Map[SBThread, Rational]
) extends ProofBraid[SimpleBraid] {

  // Implentation of ProofBraid's interface

  def resolveWith(other: SimpleBraid, resolution: R):SimpleBraid = (this.sizes, other.sizes) match {

    // Less than 2 main threads
    case ((0,_,0), (0,_,0)) =>
      mergePending(other.pending)
    case (_, (0,_,0)) =>
      mergePending(other.pending).mergeCompletePending()
    case ((0,_,0), _) =>
      other.mergePending(pending).mergeCompletePending()

    // Too simple cases
    case ((1,0,0), (1,0,0)) =>
      initBraid(R(main.get, other.main.get, resolution.auxL))

    case ((1,0,_), (1,0,_)) =>
      resolve(other.main.get, resolution.auxL).mergeMerged(other.merged).mergeCompletePending()

    // Regularisation cases
    case ((1,_,_), (1,_,_)) if (hasPending(Right(resolution.auxL))) =>
//      println("** Resolution "+Right(resolution.auxL))
      mergeMerged(other.pending).mergeMerged(other.merged).mergeCompletePending()
    case ((1,_,_), (1,_,_)) if (other.hasPending(Left(resolution.auxL))) =>
//      println("** Resolution "+Left(resolution.auxL))
      other.mergeMerged(pending).mergeMerged(merged).mergeCompletePending()

    // Delay cases
    case ((1,_,_), (1,_,_)) if !(main.get.conclusion.suc contains resolution.auxL) && (other.main.get.conclusion.ant contains resolution.auxL) =>
      mergePending(other.pending + (SBThread(other.main.get, Right(resolution.auxL)) -> Rational.one)).mergeMerged(other.merged).mergeCompletePending()
    case ((1,_,_), (1,_,_)) if (main.get.conclusion.suc contains resolution.auxL) && !(other.main.get.conclusion.ant contains resolution.auxL) =>
      other.mergePending(pending + (SBThread(main.get, Right(resolution.auxL)) -> Rational.one)).mergeMerged(merged).mergeCompletePending()


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
      val mergeLeft  = conflictGraph(Right(resolution.auxL))
      val mergeRight = conflictGraph(Left(resolution.auxL))
      val threadLeft  = (this  /:  mergeLeft.reverseOrder(SBMain(main.get)))       { _ merge _ }
      val threadRight = (other /: mergeRight.reverseOrder(SBMain(other.main.get))) { _ merge _ }

      // Step 3, 4 and 5
      threadLeft.resolve(threadRight.main.get, resolution.auxL).mergePending(threadRight.pending).mergeMerged(threadRight.merged).mergeCompletePending()


    // Catch all
    case (t,o) => throw new Exception("Unhandled situation "+t+" "+o)
  }
  
  def divise(divisor: Int, pivot: Either[E,E]) = 
    if (divisor == 1) this else {
      val pendingDivided = pending mapValues {_ / divisor}
      SimpleBraid(
        None,
        main match {
          case None => pendingDivided
          case Some(subproof) => pendingDivided + (SBThread(subproof,pivot) -> (Rational.one / divisor))
        },
        merged mapValues {_ / divisor}
      )
    }

  def finalMerge = main match {
    case Some(subproof) => println("Final "+sizes) ; subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }


  // Utils functions

  // main methods

  def resolve(subproof: SequentProofNode, pivot: E) = 
    SimpleBraid(Some(R(main.get, subproof, pivot)), pending, merged)

  // pending methods

  def hasPending(pivot: Either[E,E]) = pending exists { kv =>
    val (SBThread(_,other),_) = kv
    other == pivot
  }

  def merge(v: GraphVertex) = v match {
    case thread @ SBThread(subproof, pivot) =>
      val fraction = pending(thread)
      val nMerged = if (fraction < Rational.one) merged + (thread -> fraction) else merged
      (main, pivot) match {
        case (None, _)           => SimpleBraid(Some(subproof),          pending - thread, nMerged)
        case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - thread, nMerged)
        case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - thread, nMerged)
      }
    case _ => throw new Exception("Unable to merge non-thread")
  }

  def mergeMap(a: Map[SBThread, Rational], b: Map[SBThread, Rational]) =
    (a /: b) { (acc, kv) =>
      val (thread, fraction) = kv
      if (acc contains thread) {
        val newFraction = fraction + acc(thread)
        acc + (thread -> newFraction)
      }
      else acc + (thread -> fraction)
    }

  def mergePending(m: Map[SBThread, Rational]) = (this /: m) { (acc,kv) =>
    val (key, fraction) = kv
    if (acc.merged contains key) {
      val nfrac = fraction + acc.merged(key)
      SimpleBraid(acc.main, acc.pending + (key -> nfrac), acc.merged - key)
    }
    else {
      val nfrac = fraction + acc.pending.getOrElse(key, Rational.zero)
      SimpleBraid(acc.main, acc.pending + (key -> nfrac), acc.merged)
    }
  }

  // merged methods

  def mergeMerged(m: Map[SBThread, Rational]) = (this /: m) { (acc,kv) =>
    val (key, fraction) = kv
    if (acc.pending contains key) {
      val nfrac = fraction + acc.pending(key)
      SimpleBraid(acc.main, acc.pending + (key -> nfrac), acc.merged)
    }
    else if (acc.merged contains key) {
      val nfrac = fraction + acc.merged(key)
      if (nfrac < Rational.one) 
        SimpleBraid(acc.main, acc.pending, acc.merged + (key -> nfrac))
      else
        SimpleBraid(acc.main, acc.pending, acc.merged - key)
    }
    else
      SimpleBraid(acc.main, acc.pending, acc.merged + (key -> fraction))
  }

  // Miscellaneous (TODO: tidy it up)

  def sizes = (main.size, pending.size, merged.size)

  def conflictGraph(pivot: Either[E,E]) = {
//      println("conflictGraph")
      val graph  = new ConflictGraph[GraphVertex]()

      @tailrec
      def collectPending(pivots: Seq[Either[E,E]], parg: Map[SBThread,Rational]):Unit = {
        var p = parg
//        println(pivots)
        var nPivots = List[Either[E,E]]()

        for (key @ SBThread(subproof, pivot) <- p.keys)
          pivots foreach { _ match {
              case Left(l)  if (subproof.conclusion.ant contains l) =>
//                println("Add "+subproof.conclusion+" "+pivot)
                graph += key
                p = p - key
                nPivots = pivot::nPivots
              case Right(l) if (subproof.conclusion.suc contains l) =>
//                println("Add "+subproof.conclusion+" "+pivot)
                graph += key
                p = p - key
                nPivots = pivot::nPivots
              case _ => ()
            } }
        
        if ((nPivots.size > 0) && (p.size > 0)) collectPending(nPivots, p)

      }

      collectPending(List(pivot), pending)
      graph
  }

  def mergeCompletePending() = {
//    println("\n mergeCompletePending")
    val graph = new ConflictGraph[GraphVertex]()
    for ((key, fraction) <- pending)
      if (fraction >= Rational.one) graph += key
    (this /: graph.reverseOrder(SBMain(main.get))) { _ merge _ }
  }

}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
