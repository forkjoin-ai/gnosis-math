
namespace Gnosis

def truth_deficit (recursion_depth : Nat) : Nat := recursion_depth
def bounds (n : Nat) : Nat := n + 1

theorem truth_deficit_always_bounded (d : Nat) : truth_deficit d < bounds d :=
  Nat.lt_succ_self d

end Gnosis