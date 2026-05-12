/-!
# Coarse Observation Collapse

Init-only replacement for the planetary coarse-observation sketch.

The historical artifact proved the full finite pigeonhole theorem
`¬ Function.Injective (f : Fin (n+1) → Fin n)` with external cardinality
machinery.  This chapel module restores the concrete witness shape used by
the ledger: a coarse readout merges two neighboring fine states.
-/

namespace PlanetaryHomologySandbox

/-- Collapse the final two states of a fine `(n + 2)`-state readout into the
final state of a coarse `(n + 1)`-state readout, preserving all earlier states. -/
def coarseObservation (n : Nat) : Fin (n + 2) → Fin (n + 1)
  | ⟨k, _hk⟩ =>
      if hSmall : k < n then
        ⟨k, Nat.lt_succ_of_lt hSmall⟩
      else
        ⟨n, Nat.lt_succ_self n⟩

/-- The next-to-last fine state maps to the final coarse state. -/
theorem coarseObservation_next_to_last
    (n : Nat) :
    coarseObservation n ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ =
      ⟨n, Nat.lt_succ_self n⟩ := by
  unfold coarseObservation
  simp

/-- The last fine state also maps to the final coarse state. -/
theorem coarseObservation_last
    (n : Nat) :
    coarseObservation n ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ =
      ⟨n, Nat.lt_succ_self n⟩ := by
  unfold coarseObservation
  simp

/-- A concrete collision witness for the coarse observation map. -/
theorem coarseObservation_collides
    (n : Nat) :
    coarseObservation n ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ =
      coarseObservation n ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := by
  rw [coarseObservation_next_to_last, coarseObservation_last]

/-- The two colliding fine states are distinct. -/
theorem coarseObservation_collision_distinct
    (n : Nat) :
    (⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ : Fin (n + 2)) ≠
      ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := by
  intro h
  have hVal : n = n + 1 := Fin.val_eq_of_eq h
  exact Nat.succ_ne_self n hVal.symm

/-- The canonical coarse observation is not injective. -/
theorem coarseObservation_not_injective
    (n : Nat) :
    ¬ Function.Injective (coarseObservation n) := by
  intro hInjective
  exact coarseObservation_collision_distinct n
    (hInjective (coarseObservation_collides n))

end PlanetaryHomologySandbox
