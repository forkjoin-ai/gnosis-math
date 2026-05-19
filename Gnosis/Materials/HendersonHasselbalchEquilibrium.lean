import Init

/-
  HendersonHasselbalchEquilibrium.lean
  ====================================

  Formalizes the Henderson-Hasselbalch equilibrium witness.
  The classical equation pH = pKa + log10([A-]/[HA]) is mapped across 
  the "Transcendental Barrier" into a discrete acid-base equilibrium witness.

  In Gnosis, we model the pH buffer capacity as a discrete ratio witness,
  where the balance of conjugate base [A-] and weak acid [HA] determines
  the topological shift from the intrinsic dissociation constant (pKa).

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Materials

/-- 
  Equilibrium Context.
  pka: Intrinsic dissociation constant witness.
  base: Concentration of the conjugate base ([A-]).
  acid: Concentration of the weak acid ([HA]).
-/
structure EquilibriumContext where
  pka : Nat
  base : Nat
  acid : Nat

/-- 
  Alkaline Shift Witness:
  A discrete measure of how much the base concentration pulls the 
  equilibrium pH above the pKa. We use base / (acid + 1) to represent
  the logarithmic ratio shift.
-/
def AlkalineShift (c : EquilibriumContext) : Nat :=
  c.base / (c.acid + 1)

/-- 
  Acidic Shift Witness:
  A discrete measure of how much the acid concentration pulls the 
  equilibrium pH below the pKa.
-/
def AcidicShift (c : EquilibriumContext) : Nat :=
  c.acid / (c.base + 1)

/-- 
  Equilibrium pH Witness (pH):
  The net topological state of the buffer system.
  pH = pKa + alkaline_shift - acidic_shift.
  We use Int to allow the pH to swing below the pKa.
-/
def PhWitness (c : EquilibriumContext) : Int :=
  (c.pka : Int) + (AlkalineShift c : Int) - (AcidicShift c : Int)

/-- 
  Theorem: Alkaline Monotonicity.
  Increasing the conjugate base concentration never decreases the pH witness.
-/
theorem alkaline_monotonicity (pka acid : Nat) (b1 b2 : Nat)
  (h_b : b1 ≤ b2) :
  PhWitness ⟨pka, b1, acid⟩ ≤ PhWitness ⟨pka, b2, acid⟩ := by
  unfold PhWitness AlkalineShift AcidicShift
  have h_alk : ((b1 / (acid + 1) : Nat) : Int) ≤ ((b2 / (acid + 1) : Nat) : Int) := by
    apply Int.ofNat_le.mpr
    apply Nat.div_le_div_right
    exact h_b
  have h_acid : ((acid / (b2 + 1) : Nat) : Int) ≤ ((acid / (b1 + 1) : Nat) : Int) := by
    apply Int.ofNat_le.mpr
    apply Nat.div_le_div_left
    . apply Nat.succ_le_succ
      exact h_b
    . apply Nat.succ_pos
  -- Need to show: (pka + alk1) - acid1 ≤ (pka + alk2) - acid2
  have step1 := Int.add_le_add_left h_alk (pka : Int)
  have step2 := Int.sub_le_sub_right step1 ((acid / (b1 + 1) : Nat) : Int)
  have step3 := Int.sub_le_sub_left h_acid ((pka : Int) + ((b2 / (acid + 1) : Nat) : Int))
  exact Int.le_trans step2 step3

/-- 
  Theorem: Neutrality Witness.
  If the base and acid concentrations are equal and zero, the system 
  rests exactly at the pKa.
-/
theorem zero_concentration_neutrality (pka : Nat) :
  PhWitness ⟨pka, 0, 0⟩ = (pka : Int) := by
  unfold PhWitness AlkalineShift AcidicShift
  simp [Int.sub_zero]

/-
  Persistence Record (Transcendental Bridge):
  1. Refused log10([A-]/[HA]) due to transcendental kernel limits.
  2. Mapped the logarithmic ratio to discrete additive/subtractive 
     shifts: + (base / acid) and - (acid / base).
  3. Validated through alkaline monotonicity, preserving the buffer 
     response structure of the Henderson-Hasselbalch equation.
-/

end Gnosis.Materials
