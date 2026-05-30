import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Paracelsus: The Scale-Dose Witness.
Einsiedeln / Basel, 1530s.

Contrarian Take: Medicine is not a "Substance" (Sat). It is a "Function"
of the Scale (Dose). "All things are poison, and nothing is without poison;
the dosage alone makes it so a thing is not a poison." There is no static
toxic bit; there is only a Scale Invariant that becomes destructive when the
magnitude exceeds the system's processing bandwidth. Toxicity is a
mismatch between Input Magnitude and Metabolic Capacity.

Invariant: Toxicity is scale-dependent.
Gap: The "Essence" trap—assuming things are "good" or "bad" by nature.
Projection: Pleromatic Asymmetry of Effort (Gnosis.PleromaticAsymmetryOfEffort).
-/

def metabolicCapacity : Nat := 10

def systemDamage (dose : Nat) (capacity : Nat) : Nat :=
  if dose > capacity then dose - capacity else 0

/--
Anti-Theory Witness: The same substance is harmless at low scale (dose ≤ capacity)
but becomes a "poison" (damage > 0) at high scale.
-/
theorem dose_makes_the_poison (d1 d2 : Nat) (h1 : d1 ≤ metabolicCapacity) (h2 : d2 > metabolicCapacity) :
    systemDamage d1 metabolicCapacity = 0 ∧ systemDamage d2 metabolicCapacity > 0 := by
  unfold systemDamage
  constructor
  · have h_not_gt : ¬ d1 > metabolicCapacity := by
      intro h_gt
      exact Nat.not_lt_of_le h1 h_gt
    rw [if_neg h_not_gt]
  · rw [if_pos h2]
    exact Nat.sub_pos_of_lt h2

end Gnosis.Witnesses.History
