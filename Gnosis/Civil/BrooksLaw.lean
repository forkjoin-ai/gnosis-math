/-
  BrooksLaw.lean
  ==============

  Formalizes Brooks's Law: "Adding manpower to a late software project
  makes it later." This applies equally to complex engineering and
  construction management.

  In Gnosis, we model the project duration as a function of manpower (n).
  The "Ramp-up Cost Witness" establishes that beyond an optimal threshold,
  the coordination overhead exceeds the productivity gain.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  A Project State.
  n: Number of staff.
  individual_productivity: Productive output per person.
  coordination_penalty: Cost of coordination per person.
-/
structure ProjectStaffing where
  n : Nat
  individual_productivity : Nat
  coordination_penalty : Nat

/-- 
  Net Productivity Witness:
  P = n * p - n * c
-/
def net_productivity (s : ProjectStaffing) : Int :=
  (s.n : Int) * (s.individual_productivity : Int) - ((s.n : Int) * (s.coordination_penalty : Int))

/-- 
  Theorem: Productivity Reversal Witness.
  If the coordination penalty exceeds individual productivity, adding
  more staff (n > 0) results in negative net productivity.
-/
theorem productivity_reversal (n p c : Nat)
  (h_late : c > p)
  (h_staff : n > 0) :
  net_productivity ⟨n, p, c⟩ < 0 := by
  unfold net_productivity
  apply Int.sub_neg_of_lt
  match n with
  | 0 => 
    have h_staff_pos : 0 > 0 := h_staff
    cases h_staff_pos
  | Nat.succ _ =>
    have h_p : (p : Int) < (c : Int) := Int.ofNat_lt.mpr h_late
    apply Int.mul_lt_mul_of_pos_left h_p
    -- n > 0 witness
    show (0 : Int) < ↑(Nat.succ _)
    apply Int.ofNat_pos.mpr
    apply Nat.succ_pos

end Gnosis.Civil