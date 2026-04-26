import Lean
def testGet (a : Array Float) (i : Nat) : Float := a[i]!
#eval testGet #[1.0, 2.0] 0
