
namespace Gnosis

def oracle_stall_cost (n : Nat) : Nat := n + 1
def functorial_gain (n : Nat) : Nat := n + 2

theorem oracle_stall_overcome (n : Nat) : oracle_stall_cost n < functorial_gain n :=
  Nat.lt_succ_self (n + 1)

end Gnosis