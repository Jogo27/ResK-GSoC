package at.logic.skeptik.util.Report

import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.immutable.{Map => IMap}

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment.Sequent

abstract class Report {
  type Measurements = IMap[String,Int]
  val emptyMeasure : Measurements = IMap("length" -> 0, "coreSize" -> 0, "height" -> 0)
  def addMeasures(a: Measurements, b: Measurements) = IMap((emptyMeasure.keys map { k => (k, a(k) + b(k)) }).toSeq : _*)

  def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = ()
  def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = ()
  def terminate():Unit = ()
}

class HumanReadableReport
extends Report {
  var m = emptyMeasure
  val cumul = MMap[String, (Measurements, Double, Measurements)]()

  override def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    m = measure
    printf("\n%s\n%-16s %6d ms %7d %6.2f %% %7d %6.2f %% %7d %6.2f %%\n",
           name, "", timing.toInt, measure("length"), percent(1,1), measure("coreSize"), percent(1,1), measure("height"), percent(1,1))
  }

  def percent(o: Int, n: Int):Double = (1.0 - (n.toDouble / o.toDouble)) * 100.0

  override def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    val (oldOpM, oldTiming, oldProofM) = cumul.getOrElse(name, (emptyMeasure, 0.0, emptyMeasure))
    cumul += (name -> (addMeasures(oldOpM, measure), oldTiming + timing, addMeasures(oldProofM, m)))
    
    printf("%-16s %6d ms %7d %6.2f %% %7d %6.2f %% %7d %6.2f %%\n",
           name, timing.toInt,
           measure("length"), percent(m("length"),measure("length")),
           measure("coreSize"), percent(m("coreSize"),measure("coreSize")),
           measure("height"), percent(m("height"),measure("height")) )

  }

  override def terminate():Unit = {
    println()
    for ((name, (op, t, pr)) <- cumul) 
      printf("%-16s %4.1f n/ms %7d %6.2f %% %7d %6.2f %% %7d %6.2f %%\n",
            name, pr("length")/t,
            op("length"), percent(pr("length"),op("length")),
            op("coreSize"),  percent(pr("coreSize"),op("coreSize")),
            op("height"), percent(pr("height"),op("height")) )
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
    case _ => println(name+": error on "+proofname+", expected "+conclusion+" got "+proof.root.conclusion)
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
    if (curBest != curWorse) {
      for (op <- curBestOp)
        countBest(op) = countBest.getOrElse(op, 0) + 1
      for (op <- curWorseOp)
        countWorse(op) = countWorse.getOrElse(op, 0) + 1
    }

    curBestOp.clear
    curWorseOp.clear
    n += 1
  }

  override def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = endProof

  override def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = {
    if (curBestOp.isEmpty || (measure("length") < curBest)) { curBest = measure("length") ; curBestOp.clear() }
    if (measure("length") == curBest) curBestOp += name
    
    if (curWorseOp.isEmpty || (measure("length") > curWorse)) { curWorse = measure("length") ; curWorseOp.clear() }
    if (measure("length") == curWorse) curWorseOp += name
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
