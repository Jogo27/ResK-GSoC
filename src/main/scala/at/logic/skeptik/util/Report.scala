package at.logic.skeptik.util.Report

import collection.mutable.{HashMap => MMap, HashSet => MSet}

import at.logic.skeptik.proof.{Proof, Measurements}
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment.Sequent

abstract class Report {
  def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = ()
  def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = ()
  def terminate():Unit = ()
}

class HumanReadableReport
extends Report {
  var m = Measurements(0,0,0)
  val cumul = MMap[String, (Measurements, Double, Measurements)]()

  override def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    m = measure
    printf("\n%s\n%-16s %6d ms %7d %6.2f %% %7d %6.2f %% %7d %6.2f %%\n",
           name, "", timing.toInt, measure.length, 100.0, measure.width, 100.0, measure.height, 100.0)
  }

  def percent(o: Int, n: Int):Double = (1.0 - (n.toDouble / o.toDouble)) * 100.0

  override def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    val (oldOpM, oldTiming, oldProofM) = cumul.getOrElse(name, (Measurements(0,0,0), 0.0, Measurements(0,0,0)))
    cumul += (name -> (oldOpM + measure, oldTiming + timing, oldProofM + m))
    
    printf("%-16s %6d ms %7d %6.2f %% %7d %6.2f %% %7d %6.2f %%\n",
           name, timing.toInt,
           measure.length, percent(m.length,measure.length),
           measure.width, percent(m.width,measure.width),
           measure.height, percent(m.height,measure.height) )

  }

  override def terminate():Unit = {
    println()
    for ((name, (op, t, pr)) <- cumul) 
      printf("%-16s %4.1f n/ms %7d %6.2f %% %7d %6.2f %% %7d %6.2f %%\n",
            name, pr.length/t,
            op.length, percent(pr.length,op.length),
            op.width,  percent(pr.width,op.width),
            op.height, percent(pr.height,op.height) )
  }
}

class VerificationReport
extends Report {
  var conclusion : Option[Sequent] = None
  var proofname = ""
  
  override def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    conclusion = Some(proof.root.conclusion)
    proofname = name
  }

  override def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = conclusion match {
    case Some(c) if proof.root.conclusion subsequentOf c => ()
    case _ => println("Error with "+name+" on "+proofname)
  }
}

class BestWorseReport
extends Report {
  var curBest = 0
  val curBestOp = MSet[String]()
  val countBest = MMap[String, Int]()

  var curWorse = 0
  val curWorseOp = MSet[String]()
  val countWorse = MMap[String, Int]()

  var n = -1

  private def endProof() = {
    for (op <- curBestOp)
      countBest(op) = countBest.getOrElse(op, 0) + 1
    curBestOp.clear

    for (op <- curWorseOp)
      countWorse(op) = countWorse.getOrElse(op, 0) + 1
    curWorseOp.clear

    n += 1
  }

  override def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = endProof

  override def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    if (curBestOp.isEmpty || (measure.length < curBest)) { curBest = measure.length ; curBestOp.clear }
    if (measure.length == curBest) curBestOp += name
    
    if (curWorseOp.isEmpty || (measure.length > curWorse)) { curWorse = measure.length ; curWorseOp.clear }
    if (measure.length == curWorse) curWorseOp += name
  }

  override def terminate():Unit = {
    endProof
    println()
    val keys = countBest.keySet | countWorse.keySet
    for (op <- keys)
      printf("%-16s %4d %6.2f %% %4d %6.2f %%\n", op,
             countBest.getOrElse(op,0), 100.0 * countBest.getOrElse(op,0).toDouble / n.toDouble,
             countWorse.getOrElse(op,0), 100.0 * countWorse.getOrElse(op,0).toDouble / n.toDouble )
  }
}
