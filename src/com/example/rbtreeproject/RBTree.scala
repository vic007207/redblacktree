package com.example.rbtreeproject


import com.example.rbtreeproject.CoqMain._
import scala.collection.immutable.List
/**
 * Created by knix on 12/15/14.
 */
object RBTree {
  def toNat(x: Int): Nat = {
    var soFar: Nat = O()
    var int: Int = x;
    while (int > 0) {
      soFar = S(soFar)
      int = int - 1
    }
    soFar
  }
  def toInt(n: Nat): Int = {
    var soFar: Int = 0
    var nat: Nat = n
    while (nat != O()) {
      soFar = soFar + 1
      nat = nat match {
        case O() => O()
        case S(x) => x
      }
    }
    soFar
  }

  def rbinsert(x: Int, t: Tree) = CoqMain.insert(toNat(x))(t)

  def rbmember(x: Int, t: Tree) = CoqMain.member(toNat(x))(t) match {
    case True() => true
    case False() => false
  }

  def rbvalue(t: Tree) = CoqMain.value(t) match {
    case Some(x) => toInt(x)
    case None() => -1
  }

  def rbcolor(t: Tree) = CoqMain.color(t) match {
    case None() => None
    case Some(x) => x
  }

  def rbtraversal(t: Tree) = natListToIntList(CoqMain.traversal(t))

  def natListToIntList(ns: CoqMain.List[Nat]): List[Int] = ns match {
    case Nil() => List.empty[Int]
    case Cons(h, tail) => toInt(h) :: natListToIntList(tail)
  }


}
