import com.example.rbtreeproject.CoqMain._
import com.example.rbtreeproject.RBTree._
val zero: Nat = O()
val one: Nat = S(O())
val two: Nat = S(S(O()))
val three: Nat = S(S(S(O())))
val red: Color = R()
val empty: Tree = E()
val a: Tree = T(red, empty, three, empty)
val t1: Tree = rbinsert(1, empty)
value(t1)


val b = toNat(4)
val x = toInt(toNat(101))
val t2: Tree = rbinsert(2, t1)
traversal(t2)
value(t2)
val g = rbvalue(T(red, empty, one, empty))
val c = color(t2)
val c2 = rbcolor(t2)

val bigTree: Tree = rbinsert(1,
  rbinsert(2,
    rbinsert(3,
    rbinsert(4,
    rbinsert(100,
    rbinsert(12,
    rbinsert(0, empty)))))))
traversal(bigTree)
rbtraversal(bigTree)
member(three)(bigTree)
rbmember(3, bigTree)
rbmember(100, bigTree)
rbmember(101, bigTree)
rbtraversal(left(bigTree))
rbtraversal(right(bigTree))

