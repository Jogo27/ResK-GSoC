package at.logic.skeptik.algorithm.compressor.middleLower

case class SBThread(val subproof: SequentProofNode, val fraction: Rational) {
  def /(divisor: Int) = SBThread(subproof, fraction/divisor)
}

case class SimpleBraid(
  val main:    Option[SBThread],
  val pending: Map[Either[E,E], SBThread],
  val merged:  Seq[SBThread]
) extends ProofBraid[SimpleBraid] {

  def resolveWith(other: SimpleBraid, resolution: R):SimpleBraid = (this,other) match {

    // New pending branch
    case (SimpleBraid(Some(mtl @ SBThread(_, fl)), pl, ml), _) if (fl < 1)=>
      SimpleBraid(None, pl + (Left(resolution.pivot) -> mtl), ml).resolveWith(other, resolution)
    case (_, SimpleBraid(Some(mtr @ SBThread(_, fr)), pr, mr)) if (fr < 1)=>
      resolveWith(SimpleBraid(None, pr + (Right(resolution.pivot) -> mtr), mr), resolution)

    // Less than 2 main thread


  }
  
  def /(divisor: Int) =
    new SimpleBraid(
      main    map       {_ / divisor},
      pending mapValues {_ / divisor},
      merged  map       {_ / divisor}
    )

  def finalMerge = main match {
    case Some(SBThread(subproof,Rational.one)) => subproof
    case _ => throw new Exception("Root node doesn't have all threads")
  }
}

object r {
  implicit def convert(node: SequentProofNode) = SimpleBraid(Some(SBThread(node, Rational.one)), IMap(), Seq())
}
