package at.logic.skeptik

// Quick and Dirty imports
import at.logic.skeptik.parser.SMT2Parser

object Main {
  def main(args: Array[String]): Unit = {
    def help() = print(usageInstructions)
    
    if (args.length == 0) help()
    else if (args(0) == "-experiment") {
      if (args.length == 1) help()
      else if (args(1) == "--NDc") {
        at.logic.skeptik.experiment.proving.ProverExperiment.run(Array());
      }   
      else if (args(1) == "--compression") {
        at.logic.skeptik.experiment.compression.Experimenter.run(args.drop(2));
      } 
      else help()
    }
    else if (args(0) == "-prove") {
      
    }
    else if (args(0) == "-compress") {
      
    }
    else if (args(0) == "-quickndirty") {
      args.tail.foreach { (filename) =>
        val parser = new at.logic.skeptik.parser.SMT2Parser(filename)
        parser.getProof
        println(filename + " " + (1 to 10).map(parser.clauseSize.getOrElse(_,0)))
      }
    }
    else help()
  }
    
  private val usageInstructions = 
  """
    
  Skeptik Usage Instructions
  ==========================
      
    -experiment    : runs pre-defined experiment
      --NDc          : contextual natural deduction experiment
      --compression  : proof compression experiment
  
    -prove         : proves theorem
      [not implemented yet]
  
    -compress      : compresses proof
      [not implemented yet]
    
  """   
}
