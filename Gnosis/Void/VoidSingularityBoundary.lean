namespace Gnosis

def landauerHeatProxy (liveBranches : Nat) : Nat :=
  if liveBranches == 0 then 1000000 else 100 / liveBranches

theorem void_singularity_forces_live_branch (liveBranches : Nat)
    (hFiniteHeat : landauerHeatProxy liveBranches < 1000) :
    liveBranches > 0 := by
  by_cases h0 : liveBranches = 0
  · subst h0
    simp [landauerHeatProxy] at hFiniteHeat
  · exact Nat.pos_of_ne_zero h0

end Gnosis