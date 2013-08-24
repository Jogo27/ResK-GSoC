package at.logic.skeptik.algorithm.compressor.middleLower

import at.logic.skeptik.util.UnionFind

import collection.mutable.{HashMap => MMap, HashSet => MSet}

trait VertexAndOutgoingEdges[V] {
  def vertex: V
  def edgeTo(other: V): Boolean
}

class ConflictGraph[V, T <: VertexAndOutgoingEdges[V]] {
  protected val matrix = MMap[T,MSet[V]]()

  def +=(elt: T) =
    if (matrix contains elt) ()
    else {
      val sup = MSet[V]()
      for (other <- matrix.keys) {
        if      (elt   edgeTo other.vertex)         sup += other.vertex
        else if (other edgeTo elt.vertex) matrix(other) += elt.vertex
      }
      matrix(elt) = sup
    }

  def contains(elt: T) = matrix contains elt

  def reverseOrder(from: V):Iterator[T] = {
    val map = matrix.clone
    for (other <- map.keys) if (other edgeTo from) map(other) += from
    new ReverseOrderIterator(map, from)
  }

  class ReverseOrderIterator(val matrix: MMap[T,MSet[V]], from: V) extends Iterator[T] {
    val uf = new UnionFind[V]()
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
            cur = uf.union(cur, key.vertex)
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
            println(matrix)
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
