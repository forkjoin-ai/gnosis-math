import Init

/-!
# SimpsonsParadox

Finite Simpson's paradox witness.

Treatment A has a higher success rate than treatment B in each stratum, but
treatment B has the higher aggregate success rate. Rates are compared by
cross-multiplication over `Nat`, so no real numbers or division are needed.
-/

namespace SimpsonsParadox

/-- Treatment arms in the finite Simpson table. -/
inductive Treatment where
  | A
  | B
deriving DecidableEq, Repr

/-- Two strata: low-risk/small case and high-risk/large case. -/
inductive Stratum where
  | small
  | large
deriving DecidableEq, Repr

/-- Successes and trials for one treatment in one stratum. -/
structure TrialCell where
  successes : Nat
  trials : Nat
deriving DecidableEq, Repr

/--
Classic finite Simpson table.

Small stratum: A = 81/87, B = 234/270.
Large stratum: A = 192/263, B = 55/80.

A is better within each stratum, but B is better after aggregation.
-/
def trialCell : Treatment → Stratum → TrialCell
  | .A, .small => { successes := 81, trials := 87 }
  | .B, .small => { successes := 234, trials := 270 }
  | .A, .large => { successes := 192, trials := 263 }
  | .B, .large => { successes := 55, trials := 80 }

/-- Cross-multiplied success-rate comparison: `x/y > u/v`. -/
def BetterRate (left right : TrialCell) : Prop :=
  left.successes * right.trials > right.successes * left.trials

/-- Aggregate a treatment across the two strata. -/
def aggregateCell (treatment : Treatment) : TrialCell :=
  { successes :=
      (trialCell treatment .small).successes +
        (trialCell treatment .large).successes,
    trials :=
      (trialCell treatment .small).trials +
        (trialCell treatment .large).trials }

/-- Treatment A beats B in the small stratum. -/
theorem treatment_A_beats_B_in_small_stratum :
    BetterRate (trialCell .A .small) (trialCell .B .small) := by
  unfold BetterRate trialCell
  native_decide

/-- Treatment A beats B in the large stratum. -/
theorem treatment_A_beats_B_in_large_stratum :
    BetterRate (trialCell .A .large) (trialCell .B .large) := by
  unfold BetterRate trialCell
  native_decide

/-- Treatment B beats A after aggregation. -/
theorem treatment_B_beats_A_in_aggregate :
    BetterRate (aggregateCell .B) (aggregateCell .A) := by
  unfold BetterRate aggregateCell trialCell
  native_decide

/--
Simpson's paradox master witness: the per-stratum winner reverses after
aggregation.
-/
theorem simpsons_paradox_master :
    BetterRate (trialCell .A .small) (trialCell .B .small) ∧
    BetterRate (trialCell .A .large) (trialCell .B .large) ∧
    BetterRate (aggregateCell .B) (aggregateCell .A) := by
  exact ⟨treatment_A_beats_B_in_small_stratum,
    treatment_A_beats_B_in_large_stratum,
    treatment_B_beats_A_in_aggregate⟩

/-- The aggregate sample sizes are balanced even while stratum allocation differs. -/
theorem aggregate_trials_match :
    (aggregateCell .A).trials = (aggregateCell .B).trials := by
  unfold aggregateCell trialCell
  native_decide

/-- The aggregate reversal is driven by B's higher aggregate successes. -/
theorem aggregate_B_has_more_successes :
    (aggregateCell .A).successes < (aggregateCell .B).successes := by
  unfold aggregateCell trialCell
  native_decide

end SimpsonsParadox
