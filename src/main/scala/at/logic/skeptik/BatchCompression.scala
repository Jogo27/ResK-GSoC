package at.logic.skeptik

import java.io.{InputStreamReader, FileReader}
import collection.immutable.{Queue => IQueue, HashMap => IMap, Seq => ISeq}
import collection.mutable.{Queue => MQueue, HashMap => MMap}

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor.algorithms

import at.logic.skeptik.parser.{BatchParser, Batch, JobBatchData, TaskBatchData, OpBatchData}

object BatchCompression {
  def parseArgs(args: Array[String]): (InputStreamReader, TraversableOnce[String]) = args.toList match {
    case Nil => (new InputStreamReader(System.in), Nil)
    case filename::Nil =>
      (new FileReader(filename), Nil)
    case filename::"-"::Nil =>
      (new FileReader(filename), io.Source.stdin.getLines())
    case filename::proofsfile::Nil =>
      val s = io.Source.fromFile(proofsfile)
      val l = s.getLines
      s.close()
      (new FileReader(filename), l)
    case filename::proofs =>
      (new FileReader(filename), proofs)
  }

  def main(args: Array[String]): Unit = {
    print("Parsing args\n")
    val (batchStream, defaultProofs) = parseArgs(args)
    print("Parsing batch file\n")
    val batch = BatchParser.read(batchStream)
    print("Compiling\n")
    val runner = Runner(batch, defaultProofs)
    print("Running\n")
    runner.run()
    print("\nDone\n")
  }
}

class Runner(val job: Job) {
  def run() = for (proof <- job.proofs) {
    print("\nReading proof "+proof+"\n")
    val task = job.tasks(proof)
    for (op <- task.operations)
      print("  compress with "+op.name+"\n")
  }
}
object Runner {
  def apply(batch: Batch, defaultProofs: TraversableOnce[String]) = {
    val compiler = new Compiler(batch, defaultProofs)
    new Runner(compiler.compile())
  }
}

class Compiler(val batch: Batch, val defaultProofs: TraversableOnce[String]) {
  val jobs = MMap[String,Job]()
  val tasks= MMap[String,Task]()
//  val ops  = MMap[String,Operation]()

  def compile(): Job = (batch.run map getJob) reduce {_ + _}

  def getJob (name: String): Job       = jobs.getOrElseUpdate (name, { Job     (batch.jobs(name), this) })
  def getTask(name: String): Task      = tasks.getOrElseUpdate(name, { Task   (batch.tasks(name), this) })
//  def getOp  (name: String): Operation = ops.getOrElseUpdate  (name, { Operation(batch.ops(name), this) })
  def getAlgo(name: String): (Proof[N] => Proof[N]) = batch.ops.get(name) match {
    case Some(OpBatchData(_,algo)) => algo
    case None => algorithms(name)
  }

  def getReport(name: String): Report = throw new Exception("No such report")
}

class Job(var proofs: IQueue[String], var tasks: IMap[String, Task]) {
  def + (other: Job): Job = {
    val ret = new Job(proofs, tasks)
    for (proof <- other.proofs) {
      if (ret.tasks contains proof) {
        ret.tasks = ret.tasks + (proof -> (ret.tasks(proof) ++ other.tasks(proof)))
      } else {
        ret.proofs = ret.proofs :+ proof
        ret.tasks = ret.tasks + (proof -> other.tasks(proof))
      }
    }
    ret
  }
}
object Job {
  def apply(): Job = { new Job(IQueue[String](), IMap[String, Task]()) }

  def apply(batchData: JobBatchData, compiler: Compiler): Job = {
    val reports = batchData.reports map compiler.getReport
    val task = ((batchData.tasks map compiler.getTask) reduce {_ ++ _}) + reports

    val proofs = batchData.proofs match {
      case Seq() => compiler.defaultProofs
      case l   => l
    }

    val (q,m) = ((IQueue[String](), IMap[String,Task]()) /: proofs) { (acc, p) => (acc._1 :+ p, acc._2 + (p -> task)) }
    new Job(q,m)
  }
}

class Task(val operations: ISeq[Operation]) {
  def + (report: Report): Task = new Task(operations map {_ + report})
  def + (reports: TraversableOnce[Report]): Task = new Task(operations map {_ + reports})
  def ++ (other: Task): Task = new Task(operations ++ other.operations)
}
object Task {
  def apply(batchData: TaskBatchData, compiler: Compiler): Task = {
    new Task(batchData.operations map { arg => new Operation(arg._1, compiler.getAlgo(arg._1), arg._2 map compiler.getReport) })
  }
}

class Operation(val name: String, algorithm: Proof[N] => Proof[N], reports: Seq[Report]) {
  def + (report: Report): Operation = new Operation(name, algorithm, reports :+ report)
  def + (nReports: TraversableOnce[Report]): Operation = new Operation(name, algorithm, reports ++ nReports)
}
object Operation {
  def apply(op: OpBatchData) = { new Operation(op.name, op.algorithm, List[Report]()) }
}

abstract class Report extends ((Unit, String, Unit) => Unit)
