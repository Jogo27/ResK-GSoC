package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap, Queue => Queue}
import java.io.InputStreamReader

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}


object BatchParser
extends JavaTokenParsers with RegexParsers {
  
  def batch: Parser[Batch] = rep(line) ^^ { list => 
    val ret = new Batch()
    list foreach { ret add _ }
    ret
  }

  def line: Parser[BatchData] = (command | declaration)

  // Commands

  def command: Parser[BatchData] = runCmd

  def runCmd: Parser[RunBatchData] = "run" ~> "[" ~> rep1sep(name, ",") <~ "]" ^^ (RunBatchData(_))

  // Declarations

  def declaration: Parser[BatchData] = (jobDcl | taskDcl | opDcl)

    // Job

  def jobDcl: Parser[JobBatchData] = "Job" ~> name <~ "{" <~ repsep(jobOpt, ",") <~ "}" ^^ { name =>
    val ret = jobTmp
    ret.name = name
    jobTmp = JobBatchData()
    ret
  }

  var jobTmp = JobBatchData()

  def jobOpt: Parser[Any] = (proofsJobOpt | tasksJobOpt | reportsJobOpt)

  def proofsJobOpt: Parser[Any] = "proofs" ~> ":" ~> "[" ~> rep1sep(escString, ",") <~ "]" ^^ { list =>
    jobTmp addProofs list
  }

  def tasksJobOpt: Parser[Any] = "tasks" ~> ":" ~> "[" ~> repsep(name, ",") <~ "]" ^^ { list =>
    jobTmp addTasks list
  }

  def reportsJobOpt: Parser[Any] = "reports" ~> ":" ~> "[" ~> repsep(name, ",") <~ "]" ^^ { list =>
    jobTmp addReports list
  }

    // Task

  def taskDcl: Parser[TaskBatchData] = "Task" ~> name ~ "[" ~ repsep(taskOp, ",") <~ "]" ^^ {
    case ~(~(name, _), list) => TaskBatchData(name, list)
  }

  def taskOp: Parser[(String, List[String])] = name ~ opt("reporting" ~> rep1sep(name, ",")) ^^ {
    case ~(name, Some(list)) => (name, list)
    case ~(name, None) => (name, List())
  }

    // Operation

  def opDcl: Parser[OpBatchData] = "Operation" ~> name ~ "=" ~ algo ^^ {
    case ~(~(n,_),a) => new OpBatchData(n,a)
  }

  def algo: Parser[Proof[N] => Proof[N]] = """[a-zA-Z0-9*() ]+""".r ^^ { AlgorithmParser parse _ }


  def escString: Parser[String] = (name | quotedString)

  def quotedString: Parser[String] = '"' ~> """[^"]*""".r <~ '"'

  def name: Parser[String] = """[^ (){}\[\]:=,]+""".r

  def read(input: InputStreamReader) = 
    parseAll(batch, input) match {
      case Success(p,_) => p // TODO
      case Failure(message,_) => throw new Exception("Failure: " + message)
      case Error(message,_) => throw new Exception("Error: " + message)
    }

}

class Batch {
  val jobs  = new MMap[String, JobBatchData ]()
  val tasks = new MMap[String, TaskBatchData]()
  val ops   = new MMap[String, OpBatchData  ]()
  var run = Queue[String]()

  def add(data: BatchData): Unit = data match {
    case RunBatchData(l)  => run ++= l
    case j: JobBatchData  => jobs  += (j.name -> j)
    case t: TaskBatchData => tasks += (t.name -> t)
    case o: OpBatchData   => ops   += (o.name -> o)
  }
}

sealed abstract class BatchData

case class RunBatchData(val list: List[String]) extends BatchData

case class JobBatchData() extends BatchData {
  var name = "undef"

  private val proofs = Queue[String]()
  private val tasks  = Queue[String]()
  private val reports= Queue[String]()

  def addProofs (nProofs:  Seq[String]) = { proofs  ++= nProofs  }
  def addTasks  (nTasks:   Seq[String]) = { tasks   ++= nTasks   }
  def addReports(nReports: Seq[String]) = { reports ++= nReports }
}

case class TaskBatchData(val name: String, val operations: List[(String, List[String])]) extends BatchData

case class OpBatchData(val name: String, val algorithm: Proof[N] => Proof[N]) extends BatchData
