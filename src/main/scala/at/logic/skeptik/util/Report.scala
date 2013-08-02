package at.logic.skeptik.util.Report

import collection.mutable.{HashMap => MMap}

import at.logic.skeptik.proof.{Proof, Measurements}
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}

abstract class Report {
  def init():Unit = ()
  def newProof(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = ()
  def newOp(name: String, proof: Proof[N], timing: Double, measure: Measurements):Unit = ()
  def terminate():Unit = ()
}

class HumanReadable
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
