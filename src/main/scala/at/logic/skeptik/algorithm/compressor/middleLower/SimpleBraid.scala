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
    case ((0,_,0), _) => (other /: pending)       { _ addPending _ }
    case (_, (0,_,0)) => (this  /: other.pending) { _ addPending _ }

    // Too simple cases
    case ((1,0,0), (1,0,0)) => initBraid(R(main.get, other.main.get, resolution.auxL))

    case ((1,0,_), (1,0,_)) =>
      SimpleBraid(Some(R(main.get, other.main.get, resolution.auxL)), pending, merged).mergeMerged(other.merged)

    // Regularisation cases
    case ((1,_,_), (1,_,_)) if (hasPending(Right(resolution.auxL))) =>
      mergeMerged(other.pending).mergeMerged(other.merged)
    case ((1,_,_), (1,_,_)) if (other.hasPending(Left(resolution.auxL))) =>
      other.mergeMerged(pending).mergeMerged(merged)

    // Delay cases
    case ((1,_,_), (1,_,_)) if !(main.get.conclusion.suc contains resolution.auxL) && (other.main.get.conclusion.ant contains resolution.auxL) =>
      SimpleBraid(main, mergeMap(pending + ((other.main.get, Right(resolution.auxL)) -> Rational.one), other.pending), merged).mergeMerged(other.merged)
    case ((1,_,_), (1,_,_)) if (main.get.conclusion.suc contains resolution.auxL) && !(other.main.get.conclusion.ant contains resolution.auxL) =>
      SimpleBraid(other.main, mergeMap(other.pending + ((main.get, Left(resolution.auxL)) -> Rational.one), pending), other.merged).mergeMerged(merged)


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
      import s._
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
      val mergeBraid = new ConflictGraph[SequentProofNode,SBThreadAsVertex]()
      for ((key, fraction) <- s4braid.pending)
        if (fraction >= Rational.one) mergeBraid += key
      (s4braid /: mergeBraid.reverseOrder(s4braid.main.get)) { _ merge _ }


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
    case Some(subproof) => subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }


  // Utils functions

  def addPending(arg: (SBThread, Rational)) = {
    val (thread @ (subproof, pivot), fraction) = arg
    if (merged contains thread) {
      val nfrac = merged(thread) + fraction
      if (nfrac < 1)
        SimpleBraid(main, pending, merged + (thread -> nfrac))
      else
        SimpleBraid(main, pending, merged - thread)
    }
    else if (pending contains thread) {
      val nfrac = pending(thread) + fraction
      if (nfrac < 1)
        SimpleBraid(main, pending + (thread -> nfrac), merged)
      else (main, pivot) match {
        case (None, _)           => SimpleBraid(Some(subproof),          pending - thread, merged)
        case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - thread, merged)
        case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - thread, merged)
      }
    } else
      SimpleBraid(main, pending + (thread -> fraction), merged)
  }

  def hasPending(pivot: Either[E,E]) = pending exists { kv =>
    val ((_,other),_) = kv
    other == pivot
  }

  def merge(thread: SBThread) = {
    val (subproof, pivot) = thread
    val fraction = pending(thread)
    (main, pivot) match {
      case (None, _)           => SimpleBraid(Some(subproof),          pending - thread, merged + (thread -> fraction))
      case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - thread, merged + (thread -> fraction))
      case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - thread, merged + (thread -> fraction))
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
      if (nfrac < 1) 
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
      println("conflictGraph")
      val graph  = new ConflictGraph[SequentProofNode,SBThreadAsVertex]()

      @tailrec
      def collectPending(pivots: Seq[Either[E,E]], parg: Map[SBThread,Rational]):Unit = {
        var p = parg
        println(pivots)
        var nPivots = List[Either[E,E]]()

        for (key @ (subproof, pivot) <- p.keys)
          pivots foreach { _ match {
              case Left(l)  if (subproof.conclusion.ant contains l) =>
                println("Add "+subproof.conclusion+" "+pivot)
                graph += key
                p = p - key
                nPivots = pivot::nPivots
              case Right(l) if (subproof.conclusion.suc contains l) =>
                println("Add "+subproof.conclusion+" "+pivot)
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

}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
