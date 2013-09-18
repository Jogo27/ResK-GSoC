package at.logic.skeptik.algorithm.compressor.middleLower

import at.logic.skeptik.util.UnionFind

import collection.{GenTraversableOnce, GenSet}
import collection.immutable.{HashSet => ISet, HashMap => IMap, Map}
import collection.mutable.{HashMap => MMap}
import annotation.tailrec

trait VertexAndOutgoingEdges[V] {
  def edgeTo(other: V): Boolean
}
trait LeafWithoutOutgoingEdges[V] extends VertexAndOutgoingEdges[V] {
  def edgeTo(other: V) = false
}

class ConflictGraph[T <: VertexAndOutgoingEdges[T]](
  protected val matrix: Map[T,ISet[T]]
) {
  require(matrix forall { _._2 forall { matrix contains _ } })

  def +(elt: T) = {
    // This implementation is slow because the matrix is traversed twice.
    // TODO: Faster implementation.
//    println("before +")
//    aff()
    val (in,out) = getInOut(elt)
//    println("+ "+elt+" in "+in+" out "+out)
    val r = new ConflictGraph[T]((IMap(elt -> out) /: matrix) { (acc,kv) =>
      val (key, vOut) = kv
      if (in contains key)
        acc + (key -> (vOut + elt))
      else
        acc + kv
    })
//    println("after +")
//    r.aff()
    r
  }

  def -(elt: T) = new ConflictGraph[T]((matrix - elt) mapValues { _ - elt })

  def --(elts: GenTraversableOnce[T]) = new ConflictGraph((matrix -- elts) mapValues { _ -- elts})

  def removeIncomingTo(to: T) = new ConflictGraph(matrix mapValues { _ - to})

  def removeIncomingsTo(to: GenSet[T]) = new ConflictGraph(matrix mapValues { _ &~ to})

  def removeEdge(from: T, to: T) = new ConflictGraph(matrix map { kv => if (kv._1 == from) (kv._1 -> (kv._2 - to)) else kv })

  def removeEdges(from: T, to: GenSet[T]) = new ConflictGraph(matrix map { kv => if (kv._1 == from) (kv._1 -> (kv._2 &~ to)) else kv })

  /** Remove all the leaves except the given one
   */
  @tailrec
  final def removeLeavesBut(leaf: T):ConflictGraph[T] = // TODO: check whether using leaves and removing them all performs better
    matrix find { kv => kv._1 != leaf && kv._2.isEmpty } match {
      case Some(v) => println("Remove leaf "+v._1) ; (this - v._1).removeLeavesBut(leaf)
      case None => this
    }


  def outgoings(from: T) = matrix(from)

  def leaves = matrix.keySet filter { matrix(_).isEmpty }

  def contains(elt: T) = matrix contains elt

  def exists(filter: T => Boolean) = matrix.keys exists filter

  def size = matrix.size

  def getInOut(elt: T) =
    ((ISet[T](), ISet[T]()) /: matrix.keys) { (acc,other) =>
      val (in,out) = acc
      ( if (other edgeTo elt)   in  + other else in,
        if (elt   edgeTo other) out + other else out )
    }

  def hasPath(from: T, to: T) = {
    def search(visited: ISet[T])(from: T):Boolean =
      if (matrix(from) contains to) true
      else (matrix(from) &~ visited) exists search(visited + from)

    if (matrix contains from)
      search(ISet[T]())(from)
    else
      false
  }
    

  // Subgraphs

  def subgraph(filterElts: T => Boolean) = 
    new ConflictGraph[T]((IMap[T,ISet[T]]() /: matrix) { (acc,kv) =>
      val (key,vOut) = kv
      if (filterElts(key))
        acc + (key -> (vOut filter filterElts))
      else
        acc
    })

  /** The subgraph such that if a ∈ subgraph and a → b in the graph, then b ∈ subgraph.
   */
  def transitiveSubgraph(filterElts: T => Boolean) = {
    @tailrec
    def addVertex(remain: Set[T], m: IMap[T,ISet[T]]):IMap[T,ISet[T]] = 
      if (remain.isEmpty) m
      else {
        val vertex = remain.head
        val nMatrix = m + (vertex -> matrix(vertex))
        addVertex((remain | matrix(vertex)) &~ nMatrix.keySet, nMatrix)
      }

    val baseVertice = if (filterElts.isInstanceOf[Set[T]]) filterElts.asInstanceOf[Set[T]] else matrix.keySet filter filterElts
//    val baseVertice = matrix.keySet filter filterElts
    val ret = new ConflictGraph[T](addVertex(baseVertice, IMap()))
    println("Transitive subgraph from "+baseVertice+" gives ("+ret.size+"):")
    ret.aff()
    ret
  }


  // Cycles

  /** Find cycles a new element would introduce in the graph.
   * The new element is not added to the graph.
   *
   * @param elt the new element
   * @param in  the set of elements which would have edge to `elt`
   * @param out the set of vertice which would have edge from `elt`
   * @return a subset of `out` where each element is the start of a cycle
   */
  def getCycleBases(elt: T, in: Set[T], out: Set[T]):Set[T] = {
    val target = in + elt
    out filter { e =>
      @tailrec
      def search(from: Set[T], visited: Set[T]):Boolean =
        if (from.isEmpty) false
        else {
          val e = from.head
          if (visited contains e) search(from - e, visited)
          else if (target contains e) true
          else search((from - e) ++ matrix(e), visited + e)
        }
      search(ISet(e),ISet())
    }
  }     

  def findCycle = {
    @tailrec
    def expandPath(start: T, path: List[(T, List[List[T]])], extension: IMap[T, List[List[T]]]):Either[(T, List[List[T]]), List[T]] = path match {
      case (last, more)::q if extension contains last =>
        @tailrec
        def computePath(after: List[List[T]], next: IMap[T, List[List[T]]]):Either[IMap[T, List[List[T]]], List[T]] = after match {
          case (l @ h::_)::_ if (h == start) => Right(l ++ extension(last).head)
          case (l @ h::_)::q =>
            val paths = extension(last) map { l ++ _ }
            computePath(q, next + (h -> (next.getOrElse(h,List[List[T]]()) ++ paths)))
          case Nil  => Left(next)
        }

        computePath(more, extension) match {
          case Left(next)   => expandPath(start, q, next)
          case Right(cycle) => Right(cycle)
        }

      case _::q =>
        expandPath(start, q, extension)

      case Nil =>
        val nPath = (List[List[T]]() /: extension) { (acc,kv) => kv._2 ++ acc }
        Left((start, nPath))
    }

    val keys = matrix.keysIterator
    @tailrec
    def search(paths: List[(T, List[List[T]])]):Option[Set[T]] =
      if (keys.hasNext) {
        val start = keys.next()
        val extension = (IMap[T, List[List[T]]]() /: matrix(start)) { (acc,elt) => acc + (elt -> List(List(elt))) }
        expandPath(start, paths, extension) match {
          case Left(nPath) => search(paths :+ nPath)
          case Right(cycle) => Some(cycle.toSet)
        }
      } else None

    search(List())
  }

  /** Delete edges from the cycle (not the vertices)
   */
  def removeCycle(cycle: Set[T]) =
    new ConflictGraph(matrix map { kv =>
      val (key, vOut) = kv
      if (cycle contains key) (key, vOut &~ cycle) else kv
    })



  // sort

  /** Sort by number of incoming edges
   */
  def sortByIncoming = {
    val map = MMap[T,Int]()
    for ((from,v) <- matrix)
      for (to <- v)
        map(to) = map.getOrElse(to,0) + 1
    matrix.keys.toSeq sortWith { (a,b) => map.getOrElse(a,0) < map.getOrElse(b,0) }
  }
      

  /** Topological sort in reversed order
   */
  def reverseOrder = (matrix find { _._2.isEmpty }) match {
    case Some((from,_)) =>
      val map = MMap[T,ISet[T]]()
      for (other <- matrix.keys) if (other != from) map(other) = matrix(other)
      new ReverseOrderIterator(map, from)
    case None => throw new Exception("Cyclic graph")
  }

  /** Topological sort in reversed order
   */
  def reverseOrderFrom(from: T):Iterator[T] = {
    val map = MMap[T,ISet[T]]()
    if (matrix contains from)
      throw new NotImplementedError()
    else
      for (other <- matrix.keys) map(other) = if (other edgeTo from) matrix(other) + from else matrix(other)
//    println(map)
    new ReverseOrderIterator(map, from)
  }

  class ReverseOrderIterator(val matrix: MMap[T,ISet[T]], from: T) extends Iterator[T] {
    val uf = new UnionFind[T]()
    var cur = from
    var nextBuffer: Option[T] = None
    var cont = true

    def hasNext = nextBuffer match {
      case Some(_) => true
      case None => cont && (! matrix.isEmpty) && {
        val n = matrix find { kv =>
          val (key, set) = kv
          val nset = set.map(uf.find)
          if ((nset.size == 1) && nset(cur)) {
            cur = uf.union(cur, key)
            matrix -= key
            true
          }
          else {
            matrix(key) = nset
            false
          }
        }
        n match {
          case Some((v,_)) =>
            nextBuffer = Some(v)
            true
          case None =>
            println("None 221 size "+matrix.size)
            cont = false
            false
        }
      }
    }

    def next() =
      if (hasNext) {
        val ret = nextBuffer.get
        nextBuffer = None
        ret
      }
      else throw new NoSuchElementException()
  }

  def edges =
    (List[(T,T)]() /: matrix) { (acc,kv) =>
      val (from,vOut) = kv
      (acc /: vOut) { (acc,to) => (from,to)::acc }
    }

  def aff() =
    for ((from,to) <- edges) println("\""+from+"\" -> \""+to+"\"")

}

object ConflictGraph {
  def apply[T <: VertexAndOutgoingEdges[T]]() = new ConflictGraph[T](IMap())
}
