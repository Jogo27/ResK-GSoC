package at.logic.skeptik

import at.logic.skeptik.parser.{ProofParser,ProofParserVeriT,ProofParserSkeptik,AlgorithmParser}
import at.logic.skeptik.exporter.{ProofExporterVeriT,ProofExporterSkeptik}
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.time._
import at.logic.skeptik.util.io.{Input,Output,NoOutput,StandardOutput,FileOutput}

import collection.mutable.{HashMap=>MMap}
import language.postfixOps

object ProofCompressionCLI {

  case class Config(inputs: Seq[String] = Seq(),
                    directory: String = "",
                    algorithms: Seq[String] = Seq(), 
                    format: String = "",
                    hout: Output = StandardOutput, // human-readable output
                    mout: Output = NoOutput, // machine-readable output
                    moutHeader: Boolean = true)                

    
  val supportedProofFormats = Seq("smt2", "skeptik")
  
  def unknownFormat(filename: String) = "Unknown proof format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
  
  def completedIn(t: Double) = " (completed in " + Math.round(t) + "ms)"       
  
  def unknownAlgorithm(a: String) = "Algorithm " + a + " is unknown."

  val parser = new scopt.OptionParser[Config]("compress"){
    
    head("\nSkeptik's Command Line Interface for Proof Compression\n\n") 

    opt[String]('a', "algorithm") unbounded() action { (v, c) => 
      c.copy(algorithms = c.algorithms ++ Seq(v))
    } text("use <alg> to compress proofs") valueName("<alg>")
    
    note("""
        <alg> can be any of the following atomic algorithms:""" + "\n" +  
        at.logic.skeptik.util.pretty.mkStringMultiLine(
           at.logic.skeptik.algorithm.compressor.algorithms.keys,
           10,60,"   ") + 
    """
        or a sequential composition denoted by '(alg1*alg2*...*algN)'
    """    
    )  
    
    opt[String]("algorithms") action { (v, c) => 
      c.copy(algorithms = c.algorithms ++ Input(c.directory + v).lines) 
    } text("use algorithms listed in <file>\n") valueName("<file>")
    
    opt[String]('d', "directory") unbounded() action { (v, c) => 
      c.copy(directory = v)
    } text("set working directory to <dir>\n") valueName("<dir>")
    
    opt[String]('f', "format") action { (v, c) => 
      c.copy(format = v) 
    } validate { v =>
      if (supportedProofFormats contains v) success 
      else failure("unknown proof format: " + v)
    } text("use <format> (either 'smt2' or 'skeptik') to output compressed proofs\n") valueName("<format>")
 

    opt[String]('m', "mout") action { (v, c) =>
      c.copy(mout = Output(c.directory + v)) 
    } text("output measurements to <file>\n") valueName("<file>")
    
    opt[Unit]("disable-header") action { (_, c) =>
      c.copy(moutHeader = false) 
    } text("disable headers in csv output files\n")
    
    opt[String]('h', "hout") action { (v, c) =>
      c.copy(hout = Output(c.directory + v)) 
    } text("output human readable measurements to <file>\n") valueName("<file>")
 
    arg[String]("<proof-file>...") unbounded() optional() action { (v, c) =>
      c.copy(inputs = c.inputs ++ Seq(c.directory + v)) 
    } text("compress proof from <proof-file>\n")
    
    opt[String]('p', "proofs") action { (v, c) => 
      c.copy(inputs = c.inputs ++ (Input(c.directory + v).lines map {c.directory + _})) 
    } text("compress proofs from files listed in <file>\n") valueName("<file>")
     
    help("help") text("print this usage text")
    
    note(
    """
    Example:
      The following command processes the proof 'eq_diamond9.smt2' using the
      algorithms 'RP' and the sequential composition of 'DAGify', 'RPI' and 'LU'.
      The compressed proofs are written using 'skeptik' proof format.

      compress -a RP -a (DAGify*RPI*LU) -f skeptik examples/proofs/VeriT/eq_diamond9.smt2
      """)
  }
  
  
  
  def main(args: Array[String]): Unit = {  

    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { c =>
      
      val measures = Seq("length","coreSize","height","time")
      
      val prettyTable = new HumanReadableTable(measures)
      val stats = new CumulativeStats(measures, c.algorithms)
      val csv = new CSV(measures, c.algorithms, c.moutHeader, c.mout)
     
      c.hout.write("\n")
      
      for (filename <- c.inputs) {
        
        val proofFormat = ("""\.[^\.]+$""".r findFirstIn filename) getOrElse { throw new Exception(unknownFormat(filename)) }
        val proofName = filename.split(proofFormat)(0) // filename without extension
        val proofParser = proofFormat match {
          case ".smt2"  => ProofParserVeriT
          case ".skeptik"  => ProofParserSkeptik
        }
        
        // Reading the proof
        c.hout.write("Reading and checking proof '"+ filename +"' ...")
        val Timed(proof, tRead) = timed { proofParser.read(filename) }   
        c.hout.write(completedIn(tRead) + "\n")
        
        // Measuring the input Proof
        c.hout.write("Measuring...")
        val Timed(mIProof,tMIProof) = timed { measure(proof) }
        c.hout.write(completedIn(tMIProof) + "\n\n")
        
        val measurements = mIProof + ("time" -> Math.round(tRead).toInt)
        
        stats.processInput(proofName, measurements)
        prettyTable.processInput(proofName, measurements)
        csv.processInput(proofName, measurements)
  
        val writeProof =  {
          c.format match {
            case "smt2" => (p: Proof[N], name: String) => ProofExporterVeriT.write(p, name)
            case "skeptik" => (p: Proof[N], name: String) => ProofExporterSkeptik.write(p, name)
            case "" =>  (p: Proof[N], name: String) => { }
          }
        }

        // Compressing the proof
        for (a <- c.algorithms) {
          val algorithm = AlgorithmParser.parse(a)
          c.hout.write("\t\tCompressing with algorithm: " + a + "...")
          val Timed(p, t) = timed { algorithm(proof) }
          c.hout.write(completedIn(t) + "\n")
          
          val oProofName = proofName + "-" + a
          c.hout.write("\t\tWriting compressed proof...")
          val Timed(_,w) = timed { writeProof(p, oProofName) }
          c.hout.write(completedIn(w) + "\n")
          
          c.hout.write("\t\tMeasuring...")
          val Timed(mOProof,tMOProof) = timed { measure(p) }
          c.hout.write(completedIn(tMOProof) + "\n\n")
          
          val measurements = mOProof + ("time" -> Math.round(t).toInt)
          
          stats.processOutput(oProofName, a, measurements)
          prettyTable.processOutput(oProofName, a, measurements)
          csv.processOutput(oProofName, a, measurements)        
        }  // end of 'for (a <- algorithms)'
      } // end of 'for (filename <- config.inputs)'
      
      // Displaying proof measurements  
      c.hout.write(prettyTable)
      
      // Displaying overall statistics
      c.hout.write(stats)
         
    } getOrElse {
     
    } 
  }
  
  type M = Map[String, Int]
  
  abstract class DataAggregator {
    def processInput(name:String, measurements: M)
    def processOutput(name:String, a: String, measurements: M)
  }
      
  // measurement table initialized with its header only
  // rows with data for every input or output proof are added during execution 
  // and the table is displayed to the user (to hout) at the end
  class HumanReadableTable(measures: Seq[String]) extends DataAggregator {
    private var t: Seq[Seq[Any]] = Seq(Seq("Proof") ++ measures)
    private var currentInputMeasurements: M = null
    private def append(name: String, data: Seq[Any]) = {
      val row = Seq(name) ++ data
      t ++= Seq(row)
    }
    def processInput(name: String, measurements: M) = {
      currentInputMeasurements = measurements
      append(name, for (m <- measures) yield measurements(m))
    }
    def processOutput(name: String, a: String, measurements: M) = {
      val data = for (m <- measures) yield {
        val o = measurements(m)
        val i = currentInputMeasurements(m)
        ""+ o + " (" + (Math.round(1000.0*o/i)/10.0) + "%)"
      } 
      append(name, data)
    }
    
    override def toString = {
      "\n" + at.logic.skeptik.util.pretty.prettyTable(t) + "\n"
    }
  }

  class CumulativeStats(measures: Seq[String], algorithms: Seq[String]) extends DataAggregator {
    private val m = MMap( ("id"::(algorithms.toList)) map { (_ -> Seq(0,0,0)) } :_* )
    
    def processInput(name: String, measurements: M) = append("id", for (m <- measures) yield measurements(m)) 
    
    def processOutput(name: String, a: String, measurements: M) = append(a, for (m <- measures) yield measurements(m))
    
    private def append(a: String, d: Seq[Int]) = m(a) = (m(a) zip d) map { case (x,y) => x+y }
    
    private def normalize(a: String) = (m(a) zip m("id")) map {case (o,i) => (Math.round(1000.0*o/i)/10.0)}
    
    override def toString = {
      ("" /: m.keys) { (s, k) => s + "Cumulative stats for " + k + ": " + normalize(k).mkString("", "%, ", "%") + "\n" }
    }
    
  }
  
  class CSV(measures: Seq[String], algorithms: Seq[String], header: Boolean, out: Output) extends DataAggregator {
    // writing header if file is empty 
    if (header && (!out.isInstanceOf[FileOutput] || (out.isInstanceOf[FileOutput] && out.asInstanceOf[FileOutput].isEmpty))) out.write {
      val emptyColumns = ("" /: measures){(acc,m) => acc + ","} // n commas for n measures
      val measureHeaders = measures.mkString("",",",",")
      "Proof,Uncompressed" + emptyColumns + (""/:(for (a <- algorithms) yield a + emptyColumns )){_ + _} + "\n" +
      ","  + measureHeaders               + (""/:(for (a <- algorithms) yield measureHeaders)){_ + _}
    }
    
    def processInput(name: String, measurements: M) = {
      out.write("\n" + name + (for (m <- measures) yield measurements(m)).mkString(",",",", ","))
    }
    
    def processOutput(name: String, a: String, measurements: M) = {
      out.write((for (m <- measures) yield measurements(m)).mkString("",",", ","))
    }
    
  }
  
}
