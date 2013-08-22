package at.logic.skeptik.util

import collection.mutable.{HashMap => MMap}
import annotation.tailrec

class UnionFind[T] {
  private var elts = MMap[T,(T,Int)]()

  @tailrec
  final def update(updtElts: List[T], par: T):T = {
    val gpar = elts(par)._1
    if (par == gpar) {
      updtElts foreach { elt => elts(elt) = (par, elts(elt)._2) }
      par
    }
    else update(par::updtElts, gpar)
  }

  def find(elt: T):T =
    if (elts contains elt) {
      val par = elts(elt)._1
      if (par == elt) elt
      else update(List(), par)
    }
    else {
      elts += (elt -> (elt,1))
      elt
    }

  def union(elt1: T, elt2: T):T = {
    val top1 = find(elt1)
    val top2 = find(elt2)
    if (top1 == top2)
      top1
    else {
      val w1 = elts(top1)._2
      val w2 = elts(top2)._2
      val (eMain, eSub, wMain, wSub) =
        if (w1 > w2) (top1, top2, w1, w2)
        else         (top2, top1, w2, w1)
      elts(eSub)  = (eMain, wSub)
      elts(eMain) = (eMain, wMain + wSub)
      eMain
    }
  }

}
