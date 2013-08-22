package at.logic.skeptik.algorithm.compressor.middleLower

trait OrderedSubproof {
  def subproof: SequentProofNode
  def <(other: SequentProofNode): Boolean
}

class ConflictGraph[P, T <: OrderedSubproof[P]] {
  protected val matrix = MMap[T,MSet[SequentProofNode]]()

  def +=(elt: T) =
    if (matrix contains elt) ()
    else {
      val sup = MSet[SequentProofNode]()
      for (other <- matrix.keys) {
        if      (elt < other.subproof)           sup += other.subproof
        else if (other < elt.subproof) matrix(other) += elt.subproof
      }
      matrix(elt) = sup
    }

  def resolve(mainproof: SequentProofNode) = {
    val map = matrix.clone
    for (other <- map.keys) if (other < mainproof) map(other) += mainproof
    val uf = new UnionFind[SequentProofNode]()
    var ret = mainproof
    var curproof = mainproof

    while (! map.isEmpty)
      map find { kv =>
        val (key, set) = kv
        val nset = set.map(uf.find)
        if ((nset.size == 1) && nset(curproof)) {
          ret = R(ret, key.subproof)
          curproof = uf.union(curproof, key.subproof)
          map -= key
          true
        }
        else {
          map(key) = nset
          false
        }
      }
    ret
  }

}
