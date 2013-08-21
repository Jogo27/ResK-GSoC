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
}

case class SimpleBraid(
  val main:    Option[SBThread],
  val pending: Map[Either[E,E], SBThread],
  val merged:  Seq[SBThread]
) extends ProofBraid[SimpleBraid] {

  def resolveWith(other: SimpleBraid, resolution: R):SimpleBraid = (this,other) match {

    // Less than 2 main thread
    // TODO

    // 
    case _ => throw new Exception("Unhandled situation")
  }
  
  def divise(divisor: Int, pivot: Either[E,E]) = 
    if (divisor == 1) this else {
      val pendingDivided = pending mapValues {_ / divisor}
      new SimpleBraid(
        None,
        main match {
          case None => pendingDivided
          case Some(thread) => pendingDivided + (pivot -> (thread / divisor))
        },
        merged map {_ / divisor}
      )
    }

  def finalMerge = main match {
    case Some(SBThread(subproof,Rational.one)) => subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }
}

object r {
  implicit def initBraid(node: SequentProofNode) = SimpleBraid(Some(SBThread(node, Rational.one)), IMap(), Seq())
}
import r._

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
