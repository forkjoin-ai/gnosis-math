/-
  IribarrenNumber.lean
  ====================

  Formalizes the Iribarren Number (Surf Similarity Parameter) for
  beach breaking waves:
  ξ = tan(α) / sqrt(H/L)

  In Gnosis, we model the breaker type as a monotonic witness of
  beach slope and wave steepness.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  The Iribarren Witness (ξ):
  Higher values correspond to surging/plunging breakers;
  lower values correspond to spilling breakers.
-/
def iribarren_witness (slope : Nat) (steepness : Nat) : Nat :=
  if steepness = 0 then 0
  else slope * 100 / steepness

/-- 
  Theorem: Steeper Beach Breaker Shift.
  Increasing the beach slope (with constant wave steepness) increases
   the Iribarren witness, indicating a shift towards more energetic
   breaker types.
-/
theorem steeper_beach_higher_iribarren (s1 s2 st : Nat)
  (h_st : st > 0)
  (h_slope : s1 ≤ s2) :
  iribarren_witness s1 st ≤ iribarren_witness s2 st := by
  unfold iribarren_witness
  match st with
  | 0 => 
    -- 0 > 0 is false
    have h_st_pos : 0 > 0 := h_st
    cases h_st_pos
  | Nat.succ _ =>
    rw [if_neg (Nat.succ_ne_zero _)]
    apply Nat.div_le_div_right
    apply Nat.mul_le_mul_right
    exact h_slope

end Gnosis.Civil
