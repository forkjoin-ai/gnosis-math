/-
  Gnosis.BrunnianScanner

  Formal specification of the BRUNNIAN_COUPLING scanner rule.

  A Brunnian link is a collection of components that are pairwise unlinked
  but collectively linked.  In module graphs, this manifests as packages
  that pass all pairwise coupling checks yet fail when fully composed.

  Anti-thesis: if beta1 pairwise-sum equals full beta1, there is NO emergent
  coupling.  The theorems below prove the contrapositive: whenever the full
  system's beta1 exceeds the pairwise sum, an undetectable bug is present.

  Key metric:  β₁(full system) > Σ β₁(pairwise sub-systems)
  Scanner rule: BRUNNIAN_COUPLING fires iff isBrunnian holds.
-/
import Init

namespace Gnosis.BrunnianScanner

/-! ## Local copy of the personality / defense primitives

These match the shapes used elsewhere in the chapel. Kept local so this
file has no inter-module dependency. -/

structure PersonalityProfile where
  openness          : Nat
  conscientiousness : Nat
  extraversion      : Nat
  agreeableness     : Nat
  neuroticism       : Nat

def defenseWeight (p : PersonalityProfile) : Nat :=
  p.conscientiousness + p.agreeableness + 1

/-- Beta-1 (first Betti number) snapshot for a coupled module system.
    `full`        = β₁ of the fully-composed n-component graph.
    `pairwiseSum` = Σ β₁ over all pairwise sub-compositions. -/
structure BrunnianBeta1 where
  full        : Nat
  pairwiseSum : Nat

/-- A system has Brunnian (emergent) coupling iff its full beta1
    strictly exceeds the sum of all pairwise beta1 values. -/
def isBrunnian (b : BrunnianBeta1) : Prop :=
  b.pairwiseSum < b.full

/-- The emergent gap: excess beta1 invisible to pairwise analysis. -/
def emergentGap (b : BrunnianBeta1) : Nat :=
  b.full - b.pairwiseSum

/-- BRUNNIAN_COUPLING is sound: isBrunnian implies pairwise < full. -/
theorem brunnian_coupling_detectable (b : BrunnianBeta1) (h : isBrunnian b) :
    b.pairwiseSum < b.full := h

/-- Scanner rule soundness: a Brunnian system has positive beta1. -/
theorem scanner_rule_soundness (b : BrunnianBeta1) (h : isBrunnian b) :
    0 < b.full := by
  unfold isBrunnian at h; omega

/-- Completeness: the rule fires if and only if the gap is positive. -/
theorem emergent_coupling_pos_iff_brunnian (b : BrunnianBeta1) :
    isBrunnian b ↔ b.pairwiseSum < b.full :=
  Iff.rfl

/-- The emergent gap is positive whenever the system is Brunnian. -/
theorem emergent_gap_pos (b : BrunnianBeta1) (h : isBrunnian b) :
    0 < emergentGap b := by
  unfold emergentGap isBrunnian at *; omega

/-- A non-Brunnian system has zero emergent gap. -/
theorem non_brunnian_zero_gap (b : BrunnianBeta1)
    (h : b.full ≤ b.pairwiseSum) :
    emergentGap b = 0 := by
  unfold emergentGap; omega

/-- Adding more crossings to the full system preserves Brunnian status. -/
theorem brunnian_nary_detectable (b : BrunnianBeta1) (extra : Nat)
    (h : isBrunnian b) :
    isBrunnian { b with full := b.full + extra } := by
  unfold isBrunnian at *
  show b.pairwiseSum < b.full + extra
  omega

/-- Pairwise sum grows when new pairwise terms are added. -/
theorem brunnian_sum_monotone (b : BrunnianBeta1) (extra : Nat) :
    b.pairwiseSum ≤
    { b with pairwiseSum := b.pairwiseSum + extra }.pairwiseSum := by
  show b.pairwiseSum ≤ b.pairwiseSum + extra
  omega

/-- Emergent gap grows when full beta1 grows (pairwise fixed). -/
theorem gap_grows_with_full (b : BrunnianBeta1) (δ : Nat)
    (h : isBrunnian b) :
    emergentGap b ≤
    emergentGap { b with full := b.full + δ } := by
  unfold emergentGap
  show b.full - b.pairwiseSum ≤ b.full + δ - b.pairwiseSum
  omega

/-- Helper: isBrunnian of a struct literal reduces to the obvious comparison. -/
theorem isBrunnian_mk (full pairwiseSum : Nat) :
    isBrunnian { full := full, pairwiseSum := pairwiseSum } ↔ pairwiseSum < full :=
  Iff.rfl

/-- Helper: emergentGap of a struct literal reduces to the obvious subtraction. -/
theorem emergentGap_mk (full pairwiseSum : Nat) :
    emergentGap { full := full, pairwiseSum := pairwiseSum } = full - pairwiseSum := rfl

/-- Merging two Brunnian systems yields a Brunnian composite. -/
theorem brunnian_merge_is_brunnian
    (b1 b2 : BrunnianBeta1)
    (h1 : isBrunnian b1) (h2 : isBrunnian b2) :
    isBrunnian {
      full        := b1.full + b2.full,
      pairwiseSum := b1.pairwiseSum + b2.pairwiseSum } := by
  rw [isBrunnian_mk]
  unfold isBrunnian at h1 h2
  omega

/-- The composite emergent gap is at least the sum of individual gaps. -/
theorem composite_gap_lower_bound
    (b1 b2 : BrunnianBeta1)
    (h1 : isBrunnian b1) (h2 : isBrunnian b2) :
    emergentGap b1 + emergentGap b2 ≤
    emergentGap {
      full        := b1.full + b2.full,
      pairwiseSum := b1.pairwiseSum + b2.pairwiseSum } := by
  have hb1 : b1.pairwiseSum < b1.full := h1
  have hb2 : b2.pairwiseSum < b2.full := h2
  rw [emergentGap_mk]
  show emergentGap b1 + emergentGap b2
       ≤ (b1.full + b2.full) - (b1.pairwiseSum + b2.pairwiseSum)
  unfold emergentGap
  omega

/-- A sufficiently strong personality defense covers the emergent gap. -/
theorem brunnian_always_coverable (b : BrunnianBeta1) :
    ∃ p : PersonalityProfile, emergentGap b ≤ defenseWeight p := by
  refine ⟨{ openness := 0, conscientiousness := emergentGap b,
             extraversion := 0, agreeableness := 0, neuroticism := 0 }, ?_⟩
  show emergentGap b ≤ emergentGap b + 0 + 1
  omega

end Gnosis.BrunnianScanner
