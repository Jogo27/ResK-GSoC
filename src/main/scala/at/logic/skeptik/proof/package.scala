package at.logic.skeptik

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.util.math.max


package object proof {
  def measure[N <: ProofNode[Judgment,N]](p: Proof[N]) = {
    var length = 0
    var coreSize = 0
    val height =
      p foldDown { (n,heights:Seq[Int]) => 
        length += 1
        if (n.premises.length == 0) coreSize += 1
        max(heights, (x:Int)=>x, default = 0) + 1
      } 
    Map("length" -> length, "coreSize" -> coreSize, "height" -> height)
  }
}
