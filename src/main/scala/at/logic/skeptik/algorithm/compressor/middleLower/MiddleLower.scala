package at.logic.skeptik.algorithm.compressor.middleLower

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.E
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

class MiddleLower[T <: ProofBraid[T]] (implicit initBraid: SequentProofNode => T)
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  def apply(proof: Proof[SequentProofNode]) = {

    def compute(node: SequentProofNode, premises: Seq[T]):T =
      ( (node, premises.toList) match {
          case (resolution:R, left::right::Nil) =>
            val R(nodeLeft, nodeRight, pivot, _) = resolution
            // Dividing the braid now is very inefficient, but easy to implement.
            // TODO: use a Map[(SequentProofNode, pivot:E)] instead of foldDown's implicit map.
            val newLeft = left.divise(
              proof.childrenOf(nodeLeft) count {
                case R(n,_,p,_) if (n eq nodeLeft) && (p == pivot) => true
                case n => false
              },
              Left(pivot)
            )
            val newRight = right.divise(
              proof.childrenOf(nodeRight) count {
                case R(_,n,p,_) if (n eq nodeRight) && (p == pivot) => true
                case _ => false
              },
              Right(pivot)
            )
            println("\nResolve "+newLeft+" with "+newRight+" on "+resolution.auxL)
            val r = newLeft.resolveWith(newRight, resolution)

            // DEBUG
            println("Resolve result: "+r)
            val currentConclusion = r.effectiveConclusion
            println("Resolve before "+resolution.conclusion+" after "+currentConclusion)
            require(currentConclusion subsequentOf resolution.conclusion)
            r

          // Ugly catchall
          // TODO: change architecture in order to handle non-resolution inferences
          case _ => initBraid(node)

          // Old crap
//          case (_, Nil) => initBraid(node)
//          case _ => throw new Exception("Unhandled inference "+node.getClass()+" "+premises.size)
        }
      )

    proof.foldDown(compute).finalMerge    
  }
}

trait ProofBraid[T] {
  def resolveWith(other: T, resolution: R):T
  def divise(divisor: Int, pivot: Either[E,E]):T
  def finalMerge:Proof[SequentProofNode]
  def effectiveConclusion: Sequent
}
