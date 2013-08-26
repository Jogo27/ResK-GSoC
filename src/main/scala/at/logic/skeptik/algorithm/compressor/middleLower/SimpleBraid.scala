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
  type SBThread = (SequentProofNode, Either[E,E])
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(node), IMap(), IMap())
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
      SimpleBraid(None, mergeMap(pending, other.pending), IMap())
    case ((0,_,0), _) => // (other /: pending)       { _ addPending _ }
      SimpleBraid(other.main, mergeMap(pending, other.pending), IMap()).mergeMerged(other.merged).mergeCompletePending()
    case (_, (0,_,0)) => // (this  /: other.pending) { _ addPending _ }
      SimpleBraid(main, mergeMap(pending, other.pending), IMap()).mergeMerged(merged).mergeCompletePending()

    // Too simple cases
    case ((1,0,0), (1,0,0)) =>
      initBraid(R(main.get, other.main.get, resolution.auxL))

    case ((1,0,_), (1,0,_)) =>
      SimpleBraid(Some(R(main.get, other.main.get, resolution.auxL)), pending, merged).mergeMerged(other.merged).mergeCompletePending()

    // Regularisation cases
    case ((1,_,_), (1,_,_)) if (hasPending(Right(resolution.auxL))) =>
//      println("** Resolution "+Right(resolution.auxL))
      mergeMerged(other.pending).mergeMerged(other.merged).mergeCompletePending()
    case ((1,_,_), (1,_,_)) if (other.hasPending(Left(resolution.auxL))) =>
//      println("** Resolution "+Left(resolution.auxL))
      other.mergeMerged(pending).mergeMerged(merged).mergeCompletePending()

    // Delay cases
    case ((1,_,_), (1,_,_)) if !(main.get.conclusion.suc contains resolution.auxL) && (other.main.get.conclusion.ant contains resolution.auxL) =>
      SimpleBraid(
        main,
        mergeMap(pending + ((other.main.get, Right(resolution.auxL)) -> Rational.one), other.pending),
        merged
      ).mergeMerged(other.merged).mergeCompletePending()
    case ((1,_,_), (1,_,_)) if (main.get.conclusion.suc contains resolution.auxL) && !(other.main.get.conclusion.ant contains resolution.auxL) =>
      SimpleBraid(
        other.main,
        mergeMap(other.pending + ((main.get, Left(resolution.auxL)) -> Rational.one), pending),
        other.merged
      ).mergeMerged(merged).mergeCompletePending()


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
      val threadLeft  = (this  /:  mergeLeft.reverseOrder(main.get))       { _ merge _ }
      val threadRight = (other /: mergeRight.reverseOrder(other.main.get)) { _ merge _ }

      // Step 3 and 4
      val s4braid =
        SimpleBraid(
          Some(R(threadLeft.main.get, threadRight.main.get, resolution.auxL)),
          mergeMap(threadLeft.pending, threadRight.pending),
          IMap()
        ).mergeMerged(threadLeft.merged).mergeMerged(threadRight.merged)

      // Step 5
      s4braid.mergeCompletePending()


    // Catch all
    case (t,o) => throw new Exception("Unhandled situation "+t+" "+o)
  }
  
  def divise(divisor: Int, pivot: Either[E,E]) = 
    if (divisor == 1) this else {
      val pendingDivided = pending mapValues {_ / divisor}
      new SimpleBraid(
        None,
        main match {
          case None => pendingDivided
          case Some(subproof) => pendingDivided + ((subproof,pivot) -> (Rational.one / divisor))
        },
        merged mapValues {_ / divisor}
      )
    }

  def finalMerge = main match {
    case Some(subproof) => println("Final "+sizes) ; subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }


  // Utils functions

  def hasPending(pivot: Either[E,E]) = pending exists { kv =>
    val ((_,other),_) = kv
    other == pivot
  }

  def merge(thread: SBThread) = {
    val (subproof, pivot) = thread
    val fraction = pending(thread)
    val nMerged = if (fraction < Rational.one) merged + (thread -> fraction) else merged
    (main, pivot) match {
      case (None, _)           => SimpleBraid(Some(subproof),          pending - thread, nMerged)
      case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - thread, nMerged)
      case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - thread, nMerged)
    }
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

  def sizes = (main.size, pending.size, merged.size)

  object s {
    import language.implicitConversions
    implicit def sbthread2vertex(t: SBThread):SBThreadAsVertex = new SBThreadAsVertex(t)
    implicit def vertex2sbthread(v: SBThreadAsVertex):SBThread = v.t
    class SBThreadAsVertex(val t: SBThread) extends VertexAndOutgoingEdges[SequentProofNode] {
      def vertex = t._1
      def edgeTo(to: SequentProofNode) = t._2 match {
        case Left(l)  => to.conclusion.ant contains l
        case Right(l) => to.conclusion.suc contains l
      }
      override def toString():String = (t._1.conclusion, t._2).toString
    }
  }

  def conflictGraph(pivot: Either[E,E]) = {
      import s._
//      println("conflictGraph")
      val graph  = new ConflictGraph[SequentProofNode,SBThreadAsVertex]()

      @tailrec
      def collectPending(pivots: Seq[Either[E,E]], parg: Map[SBThread,Rational]):Unit = {
        var p = parg
//        println(pivots)
        var nPivots = List[Either[E,E]]()

        for (key @ (subproof, pivot) <- p.keys)
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
    import s._
//    println("\n mergeCompletePending")
    val graph = new ConflictGraph[SequentProofNode,SBThreadAsVertex]()
    for ((key, fraction) <- pending)
      if (fraction >= Rational.one) graph += key
    (this /: graph.reverseOrder(main.get)) { _ merge _ }
  }

}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
