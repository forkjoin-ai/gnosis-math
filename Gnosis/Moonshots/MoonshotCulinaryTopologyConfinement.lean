import Init

namespace MoonshotCulinaryTopologyConfinement

def culinaryConfinement (topologyDepth : Nat) : Nat :=
  topologyDepth + 10

theorem optimal_confinement (topologyDepth : Nat) :
  culinaryConfinement topologyDepth > topologyDepth :=
  Nat.lt_add_of_pos_right (by decide : 0 < 10)

end MoonshotCulinaryTopologyConfinement