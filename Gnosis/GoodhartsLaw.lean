import Gnosis.GodFormula

namespace Gnosis

/-!
# Goodhart's Law — When the Measure Becomes the Target

Single scalar `godWeight R v` is **strictly antitone** in the attributed
rejection count `v` (holding budget `R` fixed). Any wedge between two
attributions of the same situation — proxy vs structural truth, clean vs
adversarial measured rejects, reported vs audited counts — therefore forces a
strict gap in the weight line. That is the Init-only spine of “when a measure
becomes a target, the system finds degrees of freedom between the proxy and the
construct.”

**Strategic under-count (proxy looks better).** If `v_proxy < v_true` but both
stay inside the budget, then `godWeight R v_proxy > godWeight R v_true`: the
proxy-backed weight strictly **overstates** the weight implied by the true
rejection line.

**Adversarial inflation (measured rejects spike).** If `v_clean < v_adv`, the
same inequality reads `godWeight R v_clean > godWeight R v_adv`; see
`Gnosis.AdversarialRobustness.adversarial_is_goodhart` for the classifier story.

**Mechanism / truthfulness.** If `v_true < v_false` (lying reports more rejects
than truth), then `godWeight R v_false < godWeight R v_true` — the same
strict-antitone spine as `MechanismDesign.truthful_dominates`.

**Quantitative wedge.** `Gnosis.GodFormula.godWeight_ordered_difference` pins the
payoff gap between two attributed counts to the rejection gap exactly:
`godWeight R a - godWeight R b = b - a` for `a ≤ b ≤ R`. Goodhart is not only a
directional inequality; it fixes the **size** of the mis-incentive in Nat units.

**Conservation overlay.** For any `v ≤ R`, `godWeight R v + v = R + 1`. Two
attributions of the same budget therefore **share the same total** even when
their split between weight and rejects is manipulated — the wedge moves mass
between the two coordinates, not along `R + 1`.

Proof style matches `RUSTIC_CHURCH.md`: unfold `godWeight`, collapse `min` with
`Nat.min_eq_left`, close with Init `Nat` lemmas only (no `omega`, no `simp` on
open goals).

**Witness-layer cousin:** `Gnosis.ProtagorasManIsMeasureWitness` — *homo mensura*
as **local** truth sheets; Goodhart here is what happens when those local proxies
are **weaponized** into targets (same moral spine, different century).

**Fable cousin:** `Gnosis.BorgesOnExactitudeInScienceWitness` — the **1:1** map that
eats the territory: no remaining **slack** for a proxy to mean anything distinct.
-/

/-- **THM-GOODHART-WEDGE**: Strictly fewer attributed rejections ⇒ strictly larger
    God-weight, for any two counts inside the same budget `R`.

    This packages the common sub-proof used by proxy-vs-truth, clean-vs-adv,
    and truthful-vs-lying readings on the `godWeight` line. -/
theorem goodhart_strict_antitone (R v_lo v_hi : Nat)
    (h_lo : v_lo ≤ R) (h_hi : v_hi ≤ R) (h : v_lo < v_hi) :
    godWeight R v_lo > godWeight R v_hi := by
  unfold godWeight
  rw [Nat.min_eq_left h_lo, Nat.min_eq_left h_hi]
  exact Nat.add_lt_add_right
    (Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le h h_hi) h) 1

/-! ## Named readings (same inequality, different stories) -/

/-- **THM-GOODHART-PROXY-INFLATES**: When the proxy line under-counts rejects
    relative to structural truth, the weight computed from the proxy strictly
    exceeds the weight from truth — the ledger-side “hollow metric” reading. -/
theorem goodhart_proxy_undercounts_truth_inflates_weight (R v_proxy v_true : Nat)
    (h_proxy : v_proxy ≤ R) (h_true : v_true ≤ R) (h_gap : v_proxy < v_true) :
    godWeight R v_proxy > godWeight R v_true :=
  goodhart_strict_antitone R v_proxy v_true h_proxy h_true h_gap

/-- **THM-GOODHART-PROXY-GAP**: Quantitative shadow — the excess proxy weight
    equals exactly the missing counted rejects `v_true - v_proxy`. -/
theorem goodhart_proxy_weight_gap_equals_rejection_gap (R v_proxy v_true : Nat)
    (h_proxy : v_proxy ≤ R) (h_true : v_true ≤ R) (h_gap : v_proxy < v_true) :
    godWeight R v_proxy - godWeight R v_true = v_true - v_proxy := by
  have hle : v_proxy ≤ v_true := Nat.le_of_lt h_gap
  exact godWeight_ordered_difference R v_proxy v_true h_proxy h_true hle

/-- **THM-GOODHART-LIE-GAP**: Symmetric reading for over-reporting rejects
    (`v_true < v_false`): the payoff loss from lying equals `v_false - v_true`. -/
theorem goodhart_lie_weight_gap_equals_overreport_gap (R v_true v_false : Nat)
    (hT : v_true ≤ R) (hF : v_false ≤ R) (hLie : v_true < v_false) :
    godWeight R v_true - godWeight R v_false = v_false - v_true := by
  have hle : v_true ≤ v_false := Nat.le_of_lt hLie
  exact godWeight_ordered_difference R v_true v_false hT hF hle

/-- **THM-GOODHART-CHAIN**: A strict ladder of rejections `u < v < w` inside the
    same budget lifts through weights: `godWeight u > godWeight w`
    (stacked proxies / multi-hop attribution drift). -/
theorem goodhart_strict_antitone_chain (R u v w : Nat)
    (hu : u ≤ R) (hv : v ≤ R) (hw : w ≤ R) (huv : u < v) (hvw : v < w) :
    godWeight R u > godWeight R w :=
  Nat.lt_trans (goodhart_strict_antitone R v w hv hw hvw)
    (goodhart_strict_antitone R u v hu hv huv)

/-- **THM-GOODHART-CONSERVATION-OVERLAY**: Different attributed `v` on the same
    budget still land on the **same** conservation total `R + 1` — Goodhart moves
    mass between the weight and rejection coordinates; it does not change the
    scalar capacity line. -/
theorem goodhart_shared_conservation_line (R v₁ v₂ : Nat)
    (h₁ : v₁ ≤ R) (h₂ : v₂ ≤ R) :
    godWeight R v₁ + v₁ = godWeight R v₂ + v₂ := by
  rw [godWeight_conservation R v₁ h₁, godWeight_conservation R v₂ h₂]

/-! ## Ledger anchor -/

/-- Ledger anchor: trivial Init identity, Rustic Church–compliant (no `simp`). -/
theorem goodharts_law_ledger_anchor (n : Nat) : n * 1 = n :=
  Nat.mul_one n

end Gnosis
