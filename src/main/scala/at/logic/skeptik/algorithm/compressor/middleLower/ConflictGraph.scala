package at.logic.skeptik.algorithm.compressor.middleLower

import at.logic.skeptik.util.UnionFind

import collection.mutable.{HashMap => MMap, HashSet => MSet}

trait VertexAndOutgoingEdges[V] {
  def edgeTo(other: V): Boolean
}
trait LeafWithoutOutgoingEdges[V] extends VertexAndOutgoingEdges[V] {
  def edgeTo(other: V) = false
}

class ConflictGraph[T <: VertexAndOutgoingEdges[T]] {
  protected val matrix = MMap[T,MSet[T]]()

  def +=(elt: T) =
    if (matrix contains elt) ()
    else {
      val sup = MSet[T]()
      for (other <- matrix.keys) {
        if      (elt   edgeTo other)         sup += other
        else if (other edgeTo elt) matrix(other) += elt
      }
      matrix(elt) = sup
    }

  def contains(elt: T) = matrix contains elt

//  def getInOut(elt: T) = {
//    val in = MSet[T]()
//    val out = MSet[T]()
//    for (other <- matrix.keys) {
//      if      (elt   edgeTo other.vertex) out += other
//      else if (other edgeTo elt.vertex)    in += elt
//    }
//    (in, out)
//  }
//    
//  /** Find cycles a new element would introduce in the graph.
//   * The new element is not added to the graph.
//   *
//   * @param elt the new element
//   * @param in  the set of elements which would have edge to `elt`
//   * @param out the set of vertice which would have edge from `elt`
//   * @return a subset of `out` where each element is the start of a cycle
//   */
//  def getCycleBases(elt: T, in: Set[T], out: Set[T]):Set[T] = {
//    val target = in + elt
//    out filter { e =>
//      @tailrec
//      def search(from: Set[T], visited: Set[T]):Boolean =
//        if (from.isEmpty) false
//        else {
//          val e = from.head
//          if (visited contains e) search(from - e, visited)
//          else if (target contains e) true
//          else search((from - e) ++ matrix(e), visited + e)
//        }
//      search(ISet(e),ISet())
//    }
//  }     
    

  def reverseOrder(from: T):Iterator[T] = {
    val map = matrix.clone
    for (other <- map.keys) if (other edgeTo from) map(other) += from
    new ReverseOrderIterator(map, from)
  }

  class ReverseOrderIterator(val matrix: MMap[T,MSet[T]], from: T) extends Iterator[T] {
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

}
