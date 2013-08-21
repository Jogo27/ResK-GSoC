package at.logic.skeptik.algorithm.compressor.middleLower

//import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.E

import spire.algebra._   // provides algebraic type classes
import spire.math._      // provides functions, types, and type classes
import spire.implicits._ // provides infix operators, instances and conversions

import collection.immutable.{ HashMap => IMap }

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

  def resolveWith(other: SimpleBraid, resolution: R):SimpleBraid = (this,other) match {

    // Less than 2 main thread
    case (SimpleBraid(None,_,m), _) if (m.isEmpty) => (other /: pending)       { _ addPending _ }
    case (_, SimpleBraid(None,_,m)) if (m.isEmpty) => (this  /: other.pending) { _ addPending _ }

    // Catch all
    case _ => throw new Exception("Unhandled situation "+this+" "+other)
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

  override def toString(): String = "(" + main.size + "," + pending.size + "," + merged.size + ")"
}

object r {
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(node), IMap(), IMap())
}
import r._

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
