import Gnosis.GodFormula
import Gnosis.Hospitality

/-!
# Claim — ownership for the recursive-hospitality LIVING CITY

A civic entity CLAIMS the site (floor) where its hospitality `Hospitality.score3`
is highest. A claim is STABLE: the incumbent holds against any challenger whose
score is not strictly higher, so claimed agents STICK across ticks rather than
re-deriving their ground position every step. Displacement happens iff a strictly
higher-scoring claimant arrives — the Skyrms best-response.

Init-only, axiom-clean (propext + Quot.sound), no Mathlib.
-/

namespace Gnosis
namespace Claim

open Gnosis (godWeight)
open Gnosis.Hospitality (score3)

/-- A claim: an entity and its `score3` value at the claimed site. -/
structure Claim where
  claimant : String
  siteScore : Int
  deriving DecidableEq, Repr

/-- The incumbent holds against a challenger when its score is ≥ the challenger's.
    A tie sticks to the incumbent (no displacement on parity). -/
def holds (incumbent challenger : Claim) : Prop :=
  incumbent.siteScore ≥ challenger.siteScore

/-- THM-CLAIM-STABLE: parity-or-lower challenger does not displace the incumbent. -/
theorem claim_is_stable (incumbent challenger : Claim)
    (h : incumbent.siteScore ≥ challenger.siteScore) :
    holds incumbent challenger := h

/-- THM-STRONGER-WINS: a strictly higher score displaces the incumbent. -/
theorem stronger_claim_wins (incumbent challenger : Claim)
    (h : challenger.siteScore > incumbent.siteScore) :
    ¬ holds incumbent challenger := by
  unfold holds; omega

/-- An incumbent is displaced exactly when the challenger scores strictly higher. -/
theorem displacement_iff_strictly_higher (incumbent challenger : Claim) :
    ¬ holds incumbent challenger ↔ challenger.siteScore > incumbent.siteScore := by
  unfold holds
  exact Int.not_le

/-- The site score for an entity comes from the lexicographic hospitality trio. -/
def scoreFromTrio (primary secondary tertiary : Int) : Int :=
  score3 primary secondary tertiary

/-- Witnessed: entity (primary 2) beats entity (primary 1) regardless of bounded
    lower tiers — primary tier dominates the claim. -/
theorem example_primary_dominates :
    scoreFromTrio 2 0 0 > scoreFromTrio 1 999 999 := by
  unfold scoreFromTrio score3; decide

/-- Witnessed: equal primary, secondary breaks the tie. -/
theorem example_secondary_tiebreak :
    scoreFromTrio 5 10 0 > scoreFromTrio 5 5 999 := by
  unfold scoreFromTrio score3; decide

/-- Realized hospitality on a claimed site under congestion: the God Formula with
    budget derived from the (positive) site score and `v` = current occupancy. -/
def realizedAt (siteScore : Int) (congestion : Nat) : Nat :=
  godWeight siteScore.toNat congestion

/-- THM-CLAIM-IMPROVES: relocating to a strictly higher-scoring site (with the
    same fresh occupancy 0) does not lower the realized God-Formula payoff — so
    claim-and-stick is a best response: you only move when score strictly improves. -/
theorem claim_improves_with_higher_score (scoreLow scoreHigh : Int)
    (h0 : 0 ≤ scoreLow) (h : scoreLow < scoreHigh) :
    realizedAt scoreLow 0 ≤ realizedAt scoreHigh 0 := by
  unfold realizedAt
  rw [Gnosis.godWeight_ceiling, Gnosis.godWeight_ceiling]
  have hle : scoreLow ≤ scoreHigh := Int.le_of_lt h
  omega

/-- Witnessed Skyrms claim: moving from a congested low-score site (payoff 2) to a
    fresh higher-score site (payoff 6) strictly improves the realized payoff. -/
theorem example_skyrms_claim_best_response :
    godWeight 3 2 = 2 ∧ godWeight 5 0 = 6 ∧ godWeight 3 2 < godWeight 5 0 := by
  refine ⟨by decide, by decide, by decide⟩

end Claim
end Gnosis
