package at.logic.skeptik

import java.io.{InputStreamReader, FileReader}
import at.logic.skeptik.parser.{BatchParser, Batch}

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
    case _ => throw new Exception("Usage: cmd <batchfile> <proofsfile>")
  }

  def main(args: Array[String]): Unit = {
    val (batchStream, defaultProofs) = parseArgs(args)
    val batch = BatchParser.read(batchStream)
    val runner = Runner(batch, defaultProofs)
    runner.run()
  }
}

case class Runner(val batch: Batch, val defaultProofs: TraversableOnce[String]) {
  def run() = {
    print("It works\n")
  }
}
