import Init

/-!
# Kin Selection — the Evolutionary Payoff of the Non-Breeding Pan

`Gnosis/Evolution.lean` formalizes selection + mutation. It does not explain why
a *non-breeding* type (the pan `0`, which leaves no direct offspring) would
persist. Hamilton's kin selection does: a helper's genes spread through the kin
it aids. Inclusive fitness counts both direct offspring and relatedness-weighted
help to relatives, so a pan that teaches/helps enough kin has positive total
fitness despite zero direct reproduction.

Rustic Church: `Init` only, `Nat` arithmetic, proofs from core lemmas.
-/

namespace Gnosis.Body.KinSelection

/-- Hamilton's rule (scaled-integer form): an altruistic act is favoured when the
    relatedness-weighted benefit to recipients meets or exceeds its cost to the
    actor (`r * b ≥ c`). -/
def hamiltonHolds (relatedness benefit cost : Nat) : Prop :=
  cost ≤ relatedness * benefit

/-- Inclusive fitness = direct offspring + relatedness-weighted help to kin. -/
def inclusiveFitness (directOffspring relatedness kinHelped : Nat) : Nat :=
  directOffspring + relatedness * kinHelped

/-- A non-breeding pan agent leaves zero direct offspring. -/
def panDirectOffspring : Nat := 0

/-- **The payoff of pan**: even with zero direct offspring, a pan that is related
    to and helps at least one kin has strictly positive inclusive fitness — so a
    non-breeding helper type can be evolutionarily favoured. -/
theorem pan_payoff (relatedness kinHelped : Nat)
    (hr : 0 < relatedness) (hk : 0 < kinHelped) :
    0 < inclusiveFitness panDirectOffspring relatedness kinHelped := by
  unfold inclusiveFitness panDirectOffspring
  rw [Nat.zero_add]
  exact Nat.mul_pos hr hk

/-- With no kin helped, a non-breeding pan has zero inclusive fitness — the
    payoff is exactly the helping, nothing else. -/
theorem pan_needs_kin (relatedness : Nat) :
    inclusiveFitness panDirectOffspring relatedness 0 = 0 := by
  unfold inclusiveFitness panDirectOffspring
  rw [Nat.mul_zero, Nat.add_zero]

/-- More kin helped never lowers a helper's inclusive fitness (monotone help). -/
theorem more_help_never_hurts (d r k₁ k₂ : Nat) (h : k₁ ≤ k₂) :
    inclusiveFitness d r k₁ ≤ inclusiveFitness d r k₂ := by
  unfold inclusiveFitness
  exact Nat.add_le_add_left (Nat.mul_le_mul_left r h) d

end Gnosis.Body.KinSelection
