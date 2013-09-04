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
  val pGraph:  ConflictGraph[GraphVertex],
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
      val threadLeft  = prepareResolutionWith(SBThread(other.main.get, Right(resolution.auxL)))
      val threadRight = other.prepareResolutionWith(SBThread(main.get, Left(resolution.auxL)))

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
        pGraph,
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

  def prepareResolutionWith(other: SBThread) = {
    val (_,out) = pGraph.getInOut(other)
    val subgraph = pGraph.transitiveSubgraph(out)
    (this /: subgraph.reverseOrder(SBMain(main.get))) { _ merge _ }
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
      val fraction = pending(thread)
      val nMerged = if (fraction < Rational.one) merged + (thread -> fraction) else merged
      (main, pivot) match {
        case (None, _)           => SimpleBraid(Some(subproof),          pGraph - thread, pending - thread, nMerged)
        case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pGraph - thread, pending - thread, nMerged)
        case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pGraph - thread, pending - thread, nMerged)
      }
    case _ => throw new Exception("Unable to merge non-thread")
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
//    println("\n mergeCompletePending")
    val subgraph = pGraph.subgraph( {
      case key: SBThread => pending(key) >= Rational.one
      case _ => false
    } )
    (this /: subgraph.reverseOrder(SBMain(main.get))) { _ merge _ }
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

}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
