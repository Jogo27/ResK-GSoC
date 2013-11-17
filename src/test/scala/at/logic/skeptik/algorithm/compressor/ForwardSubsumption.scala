package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor.subsumption._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.parser._
import at.logic.skeptik.proof.measure

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.expression.Var

//@RunWith(classOf[JUnitRunner])
//class ForwardSubsumptionSpecification extends SpecificationWithJUnit {
object ForwardSubsumptionSpecification {
  def main(args: Array[String]):Unit = {
	  val a = new Var("a",i)
    val b = new Var("b",i)
    val c = new Var("c",i)
    val d = new Var("d",i)
    val e = new Var("e",i)

	  val testcase = 1
	  var concseq:SequentProofNode = null
	  
	  if (testcase == 0) {
	    val sq1 = new Sequent(Seq(a,d),Seq())
      val sq2 = new Sequent(Seq(a,b),Seq(d))
      val sq3 = new Sequent(Seq(e),Seq(b))
      val sq4 = new Sequent(Seq(c,b),Seq(e))
      val sq5 = new Sequent(Seq(),Seq(a))
      val sq6 = new Sequent(Seq(),Seq(b))
      val sq7 = new Sequent(Seq(),Seq(c))
      
      val ax1 = new Axiom(sq1)
      val ax2 = new Axiom(sq2)
      val ax3 = new Axiom(sq3)
      val ax4 = new Axiom(sq4)
      val ax5 = new Axiom(sq5)
      val ax6 = new Axiom(sq6)
      val ax7 = new Axiom(sq7)
      
      
      val r1 = R.apply(ax1, ax2)
      val r2 = R.apply(r1,ax3)
      val r3 = R.apply(r2,ax4)
      val r4 = R.apply(r3,ax5)
      val r5 = R.apply(r4,ax6)
      concseq = R.apply(r5,ax7)
	  }
	  else {
	    val n1 = new Axiom(new Sequent(Seq(a,b),Seq()))
      val n2 = new Axiom(new Sequent(Seq(),Seq(a,b)))
      val n3 = new Axiom(new Sequent(Seq(a),Seq()))
      val n4 = R(n2,n3)
      val n5 = R(n1,n4)
      val n6 = new Axiom(new Sequent(Seq(),Seq(a)))
	    concseq = R(n5,n6)
	  }
    
    
    val proof = Proof(concseq:SequentProofNode)
//    val proof = ProofParserVeriT.read("F:/Proofs/small-size/iso_icl381.smt2")
    println(proof)
    val cproof = TopDownSubsumption(proof)
    println(cproof)
    println(cproof.root)
    println(measure(NaiveTopDownSubsumption(proof)))
    println(measure(DAGify(proof)))
//    proof bottomUp({ ((node: SequentProofNode, children: Seq[SequentProofNode]) => { print(node.conclusion + " XX " ) ; children.foreach(f => print(f.conclusion)) ; print("\n") ; node } ) } )
	
//    "Forward Subsumption" should {
//      "compress the proof" in {
//        val compproof = TopDownLeftRightSubsumption.apply(r6)
//        proof.size must beGreaterThan(compproof.size)
//      }
//      "conclude the empty clause" in {
//        val compproof = TopDownLeftRightSubsumption.apply(r6)
//        compproof.root.conclusion.isEmpty must beTrue
//      }
	}
}