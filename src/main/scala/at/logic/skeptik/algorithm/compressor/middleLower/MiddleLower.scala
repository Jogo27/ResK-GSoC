package at.logic.skeptik.algorithm.compressor.middleLower

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._

class MiddleLower[T <: ProofBraid[T]] (implicit convert: SequentProofNode => T)
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  def apply(proof: Proof[SequentProofNode]) = {

    def compute(node: SequentProofNode, premises: Seq[T]):T =
      ( (node, premises) match {
          case (resolution :R, left::right::Nil) => left.resolveWith(right, resolution)
          case (_, Nil) => convert(node)
          case _ => throw new Exception("Unhandled inference")
        }
      ) / proof.childrenOf(node).size

    proof.foldDown(compute).finalMerge    
  }
}

trait ProofBraid[T] {
  def resolveWith(other: T, resolution: R):T
  def /(divisor: Int):T //TODO: replace Int by a more generic type
  def finalMerge:Proof[SequentProofNode]
}
