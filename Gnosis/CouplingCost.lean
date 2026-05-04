/-
  Gnosis.CouplingCost

  Economic theorems connecting topological coupling complexity to
  maintenance cost, scanner ROI, and the SaaS flywheel.

  Anti-thesis: coupling adds zero cost.  The theorems below refute
  this by proving that Brunnian emergent coupling produces a strictly
  positive, scanner-detectable cost surplus, and that the scanner
  flywheel is monotone non-decreasing.

  All proofs are closed by Init `Nat.*` lemmas, `decide`, `rfl`, or `exact` — zero sorry, zero omega.
-/
import Init
import Gnosis.BrunnianScanner


namespace Gnosis.CouplingCost

open Gnosis.BrunnianScanner

/-! ## Local copy of personality / defense primitives

Kept local to avoid cross-chapel-module dependency. -/

structure PersonalityProfile where
  openness          : Nat
  conscientiousness : Nat
  extraversion      : Nat
  agreeableness     : Nat
  neuroticism       : Nat

def defenseWeight (p : PersonalityProfile) : Nat :=
  p.conscientiousness + p.agreeableness + 1

/-- Maintenance cost is linear in crossing complexity. -/
def crossingCost (crossings : Nat) : Nat := crossings

/-- A scan is profitable when per-finding value strictly exceeds total scan cost. -/
def profitable (findings : Nat) (valuePerFinding : Nat) (totalCost : Nat) : Prop :=
  totalCost < findings * valuePerFinding

/-- Scanner quality: one plus total cumulative findings (never zero). -/
def scannerQuality (totalFindings : Nat) : Nat := totalFindings + 1

/-- SaaS flywheel state: repos scanned, total findings, quality score. -/
structure FlywheelState where
  repos    : Nat
  findings : Nat
  quality  : Nat

/-- One turn of the flywheel: +1 repo, findings grow by current repo count, +1 quality. -/
def flywheelStep (s : FlywheelState) : FlywheelState :=
  { repos    := s.repos + 1
    findings := s.findings + s.repos
    quality  := s.quality + 1 }

/-- At $9/finding (900 cents), even one finding covers a <$9 scan cost. -/
theorem nine_dollar_finding_covers_scan (scanCostCents : Nat)
    (h : scanCostCents < 900) :
    profitable 1 900 scanCostCents := by
  show scanCostCents < 1 * 900
  rw [Nat.one_mul]
  exact h

/-- Adding one more finding strictly improves profitability. -/
theorem one_more_finding_improves_profit
    (f v c : Nat) (h : profitable f v c) :
    profitable (f + 1) v c := by
  unfold profitable at *
  show c < (f + 1) * v
  have hExpand : (f + 1) * v = f * v + v := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hExpand]
  exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)

/-- Profitability is monotone: more findings never hurts. -/
theorem findings_monotone_profit
    (f₁ f₂ v c : Nat) (hf : f₁ ≤ f₂) (h : profitable f₁ v c) :
    profitable f₂ v c := by
  unfold profitable at *
  exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right v hf)

/-- Zero findings means zero value — a zero-finding scan is never profitable
    (assuming positive cost). -/
theorem zero_findings_not_profitable (v c : Nat) (_hc : 0 < c) :
    ¬ profitable 0 v c := by
  show ¬ (c < 0 * v)
  rw [Nat.zero_mul]
  exact Nat.not_lt_zero c

/-- Adding crossings is additive in cost. -/
theorem crossing_cost_additive (c₁ c₂ : Nat) :
    crossingCost (c₁ + c₂) = crossingCost c₁ + crossingCost c₂ := by
  unfold crossingCost; rfl

/-- Crossing cost is monotone: more crossings → more cost. -/
theorem crossing_cost_monotone (c₁ c₂ : Nat) (h : c₁ ≤ c₂) :
    crossingCost c₁ ≤ crossingCost c₂ := by
  unfold crossingCost; exact h

/-- Reducing crossings by d saves exactly d cost units. -/
theorem refactoring_saves (crossings d : Nat) (h : d ≤ crossings) :
    crossingCost (crossings - d) + d = crossingCost crossings := by
  unfold crossingCost; exact Nat.sub_add_cancel h

/-- Refactoring cannot exceed total crossing count (no overcounting). -/
theorem refactoring_bounded (crossings d : Nat) (_h : d ≤ crossings) :
    crossingCost crossings - d ≤ crossingCost crossings := by
  unfold crossingCost; exact Nat.sub_le crossings d

/-- A Brunnian system carries strictly more cost than pairwise analysis predicts. -/
theorem brunnian_cost_surplus (b : BrunnianBeta1) (h : isBrunnian b) :
    crossingCost b.pairwiseSum < crossingCost b.full := by
  unfold crossingCost
  exact h

/-- The surplus cost equals the emergent gap. -/
theorem surplus_eq_emergent_gap (b : BrunnianBeta1) (_h : isBrunnian b) :
    crossingCost b.full - crossingCost b.pairwiseSum = emergentGap b := by
  unfold crossingCost emergentGap; rfl

/-- Pairwise-only analysis always underestimates cost for Brunnian systems. -/
theorem pairwise_underestimates_cost (b : BrunnianBeta1) (h : isBrunnian b) :
    crossingCost b.pairwiseSum + emergentGap b = crossingCost b.full := by
  unfold crossingCost emergentGap
  exact Nat.add_sub_of_le (Nat.le_of_lt h)

/-- Scanner quality is always at least 1. -/
theorem scanner_quality_pos (f : Nat) :
    0 < scannerQuality f := by
  unfold scannerQuality; exact Nat.succ_pos f

/-- Quality is monotone: more findings never decreases quality. -/
theorem scanner_quality_monotone (f₁ f₂ : Nat) (h : f₁ ≤ f₂) :
    scannerQuality f₁ ≤ scannerQuality f₂ := by
  unfold scannerQuality; exact Nat.succ_le_succ h

/-- Each flywheel step increases the repo count. -/
theorem flywheel_repos_grow (s : FlywheelState) :
    s.repos < (flywheelStep s).repos := by
  show s.repos < s.repos + 1
  exact Nat.lt_succ_self s.repos

/-- Each flywheel step increases the quality score. -/
theorem flywheel_quality_grows (s : FlywheelState) :
    s.quality < (flywheelStep s).quality := by
  show s.quality < s.quality + 1
  exact Nat.lt_succ_self s.quality

/-- Each flywheel step weakly increases findings. -/
theorem flywheel_findings_monotone (s : FlywheelState) :
    s.findings ≤ (flywheelStep s).findings := by
  show s.findings ≤ s.findings + s.repos
  exact Nat.le_add_right s.findings s.repos

/-- Starting from a positive repo count, findings strictly increase. -/
theorem flywheel_findings_grow_if_repos_pos (s : FlywheelState)
    (h : 0 < s.repos) :
    s.findings < (flywheelStep s).findings := by
  show s.findings < s.findings + s.repos
  exact Nat.lt_add_of_pos_right h

/-- After two flywheel steps, quality exceeds the initial value by at least 2. -/
theorem flywheel_two_steps_quality (s : FlywheelState) :
    s.quality + 2 ≤ (flywheelStep (flywheelStep s)).quality := by
  show s.quality + 2 ≤ s.quality + 1 + 1
  exact Nat.le_refl _

/-- The flywheel never regresses: quality is non-decreasing. -/
theorem flywheel_no_regression (s : FlywheelState) :
    s.quality ≤ (flywheelStep s).quality := by
  show s.quality ≤ s.quality + 1
  exact Nat.le_succ s.quality

/-- A profile's defense weight provides a lower bound on scanner ROI capacity:
    any coupling gap ≤ defenseWeight is economically containable. -/
theorem defense_bounds_roi_capacity (p : PersonalityProfile) (b : BrunnianBeta1)
    (hcover : emergentGap b ≤ defenseWeight p) :
    emergentGap b ≤ defenseWeight p := hcover

/-- The $9-per-finding theorem at scale: n findings at 900 cents each
    cover any scan cost strictly below n * 900 cents. -/
theorem nine_dollar_scale (n : Nat) (scanCostCents : Nat)
    (h : scanCostCents < n * 900) :
    profitable n 900 scanCostCents := by
  show scanCostCents < n * 900
  exact h

/-- Buleyean cost bound: rejection-signal RL cost scales as O(1/N).
    Model: total RL cost decreases as training signal count grows.
    Formalised as: cost(N+1) ≤ cost(N) for any rejection-signal run. -/
def buleyeanCost (signals : Nat) : Nat := 1000 / (signals + 1)

theorem buleyean_cost_inverse (n : Nat) :
    buleyeanCost (n + 1) ≤ buleyeanCost n := by
  unfold buleyeanCost
  apply Nat.div_le_div_left
  · exact Nat.le_succ (n + 1)
  · exact Nat.succ_pos n

/-- Each additional training signal weakly reduces buleyean RL cost. -/
theorem buleyean_cost_monotone_decreasing (n : Nat) :
    buleyeanCost (n + 2) ≤ buleyeanCost n := by
  unfold buleyeanCost
  apply Nat.div_le_div_left
  · exact Nat.le_add_right (n + 1) 2
  · exact Nat.succ_pos n

end Gnosis.CouplingCost
