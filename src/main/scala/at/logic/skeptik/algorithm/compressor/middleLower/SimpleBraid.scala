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

    case ((1,_,0), (1,0,0)) =>
      val threadLeft = (this /: pending) { (acc, kv) =>
        val (key @ (subproof, pivot), _) = kv
        if (pivot == Right(resolution.auxL)) throw new NotImplementedError()
        else if (subproof.conclusion.suc contains resolution.auxL) acc.merge(key)
        else acc
      }
      SimpleBraid(Some(R(threadLeft.main.get, other.main.get, resolution.auxL)), threadLeft.pending, threadLeft.merged)

    case ((1,0,_), (1,0,_)) =>
      SimpleBraid(Some(R(main.get, other.main.get, resolution.auxL)), pending, mergeMerged(merged, other.merged))

    // Main case
    case ((1,_,_), (1,_,_)) =>
      // Step 1: Merge for the resolution
      val s1threadLeft = (this /: pending) { (acc, kv) =>
        val (key @ (subproof, pivot), _) = kv
        if (pivot == Right(resolution.auxL)) throw new NotImplementedError()
        else if (subproof.conclusion.suc contains resolution.auxL) acc.merge(key)
        else acc
      }
      val s1threadRight = (other /: other.pending) { (acc, kv) =>
        val (key @ (subproof, pivot), _) = kv
        if (pivot == Left(resolution.auxL)) throw new NotImplementedError()
        else if (subproof.conclusion.ant contains resolution.auxL) acc.merge(key)
        else acc
      }

      // Step 2: Merge if the other branch has already merge
      val s2threadLeft = (s1threadLeft /: s1threadRight.merged) { (acc, kv) =>
        val (key, _) = kv
        if (acc.pending contains key) acc.merge(key)
        else acc
      }
      val s2threadRight = (s1threadRight /: s1threadLeft.merged) { (acc, kv) =>
        val (key, _) = kv
        if (acc.pending contains key) acc.merge(key)
        else acc
      }
      // Step 3: Resolution
      val s3subproof = R(s2threadLeft.main.get, s2threadRight.main.get, resolution.auxL)
      // Step 4: Merge pending
      val (s4subproof, s4pending) = ((s3subproof, s2threadLeft.pending) /: s2threadRight.pending) { (acc, kv) =>
        val (mainproof, p) = acc
        val (key @ (subproof, pivot), fraction) = kv
        val nfrac = p.getOrElse(key,Rational.zero) + fraction
        if (nfrac < 1) (mainproof, p + (key -> nfrac))
        else pivot match {
          case Left(l)  => (R(subproof, mainproof, l), p - key)
          case Right(l) => (R(mainproof, subproof, l), p - key)
        }
      }
      // Step 5: Merge merged
      val s5merge = mergeMerged(s2threadLeft.merged, s2threadRight.merged)

      SimpleBraid(Some(s4subproof), s4pending, s5merge)


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

  def merge(thread: SBThread) = {
    val (subproof, pivot) = thread
    val fraction = pending(thread)
    (main, pivot) match {
      case (None, _)           => SimpleBraid(Some(subproof),          pending - thread, merged + (thread -> fraction))
      case (Some(s), Left(p))  => SimpleBraid(Some(R(subproof, s, p)), pending - thread, merged + (thread -> fraction))
      case (Some(s), Right(p)) => SimpleBraid(Some(R(s, subproof, p)), pending - thread, merged + (thread -> fraction))
    }
  }

  def mergeMerged(a: Map[SBThread, Rational], b: Map[SBThread, Rational]) =
    (a /: b) { (acc, kv) =>
      val (thread, fraction) = kv
      if (acc contains thread) {
        val newFraction = fraction + acc(thread)
        if (newFraction < 1)
          acc + (thread -> newFraction)
        else
          acc - thread
      }
      else acc + (thread -> fraction)
    }

  def sizes = (main.size, pending.size, merged.size)
}

object SimpleMiddleLower extends MiddleLower[SimpleBraid]
