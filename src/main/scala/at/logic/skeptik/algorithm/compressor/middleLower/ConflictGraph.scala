package at.logic.skeptik.algorithm.compressor.middleLower

import at.logic.skeptik.util.UnionFind

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

  def contains(elt: T) = matrix contains elt

  def size = matrix.size

  def getInOut(elt: T) =
    ((ISet[T](), ISet[T]()) /: matrix.keys) { (acc,other) =>
      val (in,out) = acc
      ( if (other edgeTo elt)   in  + other else in,
        if (elt   edgeTo other) out + other else out )
    }
    
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
  def transitiveSubgraph(baseVertice: ISet[T]) = {
    @tailrec
    def addVertex(remain: ISet[T], m: IMap[T,ISet[T]]):IMap[T,ISet[T]] = 
      if (remain.isEmpty) m
      else {
        val vertex = remain.head
        val nMatrix = m + (vertex -> matrix(vertex))
        addVertex((remain | matrix(vertex)) &~ nMatrix.keySet, nMatrix)
      }

    new ConflictGraph[T](addVertex(baseVertice, IMap()))
  }

  def reverseOrder(from: T):Iterator[T] = {
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
//            println(matrix)
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
    for ((from,to) <- edges) println(from+" -> "+to)
      

}

object ConflictGraph {
  def apply[T <: VertexAndOutgoingEdges[T]]() = new ConflictGraph[T](IMap())
}
