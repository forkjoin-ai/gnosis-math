import Gnosis.GodFormula

namespace GossipProtocol

open Gnosis (godWeight)

structure GossipSetup where
  totalNodes : Nat
  infectedNodes : Nat
  susceptibleNodes : Nat
  hConservation : infectedNodes + susceptibleNodes = totalNodes

theorem infection_identity (setup : GossipSetup) :
    godWeight setup.totalNodes setup.susceptibleNodes = setup.infectedNodes + 1 := by
  unfold godWeight
  have hLe : setup.susceptibleNodes ≤ setup.totalNodes := by
    rw [← setup.hConservation]
    exact Nat.le_add_left setup.susceptibleNodes setup.infectedNodes
  rw [Nat.min_eq_left hLe]
  rw [← setup.hConservation]
  simp

end GossipProtocol