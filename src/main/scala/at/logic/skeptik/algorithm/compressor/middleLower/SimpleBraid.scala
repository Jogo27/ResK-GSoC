package at.logic.skeptik.algorithm.compressor.middleLower

//import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.E

import spire.algebra._   // provides algebraic type classes
import spire.math._      // provides functions, types, and type classes
import spire.implicits._ // provides infix operators, instances and conversions

import collection.immutable.{ HashMap => IMap }

object r {
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(node), IMap(), IMap())
}
import r._

case class SBThread(val subproof: SequentProofNode, val fraction: Rational) {
  def /(divisor: Int) = SBThread(subproof, fraction/divisor)
  def +(other: SBThread) =
    if (subproof eq other.subproof)
      SBThread(subproof, fraction + other.fraction)
    else
      throw new Exception("Adding different threads")
}

case class SimpleBraid(
  val main:    Option[SequentProofNode],
  val pending: Map[Either[E,E], SBThread],
  val merged:  Map[SequentProofNode, Rational]
) extends ProofBraid[SimpleBraid] {

  // Implentation of ProofBraid's interface

  def resolveWith(other: SimpleBraid, resolution: R):SimpleBraid = (this.sizes, other.sizes) match {

    // Less than 2 main thread
    case ((0,_,0), _) => (other /: pending)       { _ addPending _ }
    case (_, (0,_,0)) => (this  /: other.pending) { _ addPending _ }

    // Too simple case
    case ((1,0,0), (1,0,0)) => initBraid(R(main.get, other.main.get, resolution.auxL))

    case ((1,_,0), (1,0,0)) if !(pending contains Right(resolution.auxL)) =>
      val threadLeft = (this /: pending) { (acc, kv) =>
        val (pivot , thread @ SBThread(subproof, _)) = kv
        if (subproof.conclusion.suc contains resolution.auxL) acc.merge(pivot)
        else acc
      }
      SimpleBraid(Some(R(threadLeft.main.get, other.main.get, resolution.auxL)), threadLeft.pending, threadLeft.merged)

    case ((1,0,_), (1,0,_)) =>
      SimpleBraid(Some(R(main.get, other.main.get, resolution.auxL)), pending, mergeMerged(merged, other.merged))



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
          case Some(subproof) => pendingDivided + (pivot -> SBThread(subproof, Rational.one / divisor))
        },
        merged mapValues {_ / divisor}
      )
    }

  def finalMerge = main match {
    case Some(subproof) => subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }


  // Utils functions

  def addPending(arg: (Either[E,E], SBThread)) = {
    val (pivot, thread @ SBThread(subproof, fraction)) = arg
    if (merged contains subproof) {
      val nfrac = merged(subproof) + fraction
      if (nfrac < 1)
        SimpleBraid(main, pending, merged + (subproof -> nfrac))
      else
        SimpleBraid(main, pending, merged - subproof)
    }
    else if (pending contains pivot) {
      val nThread = pending(pivot) + thread
      if (nThread.fraction < 1)
        SimpleBraid(main, pending + (pivot -> nThread), merged)
      else (main, pivot) match {
        case (None, _)           => SimpleBraid(Some(subproof),          pending - pivot, merged)
        case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - pivot, merged)
        case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - pivot, merged)
      }
    } else
      SimpleBraid(main, pending + (pivot -> thread), merged)
  }

  def merge(pivot: Either[E,E]) = {
    val SBThread(subproof, fraction) = pending(pivot)
    (main, pivot) match {
      case (None, _)           => SimpleBraid(Some(subproof),          pending - pivot, merged + (subproof -> fraction))
      case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - pivot, merged + (subproof -> fraction))
      case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - pivot, merged + (subproof -> fraction))
    }
  }

  def mergeMerged(a: Map[SequentProofNode, Rational], b: Map[SequentProofNode, Rational]) =
    (a /: b) { (acc, kv) =>
      val (subproof, fraction) = kv
      if (acc contains subproof) {
        val newFraction = fraction + acc(subproof)
        if (newFraction < 1)
          acc + (subproof -> newFraction)
        else
          acc - subproof
      }
      else acc + (subproof -> fraction)
    }

  def sizes = (main.size, pending.size, merged.size)
}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
