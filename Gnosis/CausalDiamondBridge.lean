import Init
import Gnosis.CausalDiamond
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate
import Gnosis.AckermannLightConeBridge
import Gnosis.AckermannMonotone
import Gnosis.InformationLightCone

/-
  CausalDiamondBridge.lean
  ========================

  Integrates the "Ackermann ceiling occupies the role of c" program with the
  pre-existing `Gnosis.CausalDiamond` kernel (fork / race / fold / contains).

  The bridge already reuses `CausalDiamond.inFutureLightCone` and
  `intervalSquared` definitionally. This module closes the loop at the
  STRUCTURE level: a subluminal event sits inside a concrete causal diamond
  (`CausalDiamond.contains`), born at the origin and dying at a future apex.
  Hence every 100%-certified (computable) runtime sample lives inside a genuine
  `CausalDiamond` — the same objects the kernel forks, races, and folds.

  Init + the kernel + the bridge. Zero `sorry`, zero new `axiom`.
-/

namespace CausalDiamondBridge

open Gnosis.CausalDiamond
open AckermannFunction
open AckermannRuntimeCertificate
open AckermannLightConeBridge

/-- The Ackermann ceiling is positive everywhere — every diagonal value is at
    least 1, so the runtime diamonds below are non-degenerate. -/
theorem ackermannCeiling_pos (n : Nat) : 1 ≤ ackermannCeiling n := by
  show 1 ≤ ackermannDiag n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [ack_0]
  · show 1 ≤ hyperop n n n
    exact AckermannMonotone.pos n n n (by omega) (by omega)

/-- A subluminal event `(t, x)` is in the past light cone of the apex
    `(2t+2, 0)`. -/
theorem subluminal_in_past_cone (t : Nat) (x : Int) (h : x.natAbs ≤ t) :
    inPastLightCone { time := (↑(2 * t + 2) : Int), space := 0 }
      { time := (t : Int), space := x } = true := by
  unfold inPastLightCone
  rw [decide_eq_true_iff]
  refine ⟨by show (t : Int) ≤ (↑(2 * t + 2) : Int); omega, ?_⟩
  have hsq : x * x ≤ (t : Int) * (t : Int) := by
    have hnat : x.natAbs * x.natAbs ≤ t * t := Nat.mul_self_le_mul_self h
    have hc : ((x.natAbs * x.natAbs : Nat) : Int) ≤ ((t * t : Nat) : Int) := by
      exact_mod_cast hnat
    rwa [Int.natAbs_mul_self, Int.natCast_mul] at hc
  have htt : (t : Int) * (t : Int) ≤ ((t : Int) + 2) * ((t : Int) + 2) := by
    have hn : t * t ≤ (t + 2) * (t + 2) := Nat.mul_self_le_mul_self (by omega)
    exact_mod_cast hn
  have e1 : x - 0 = x := by omega
  have e2 : (t : Int) - (↑(2 * t + 2) : Int) = -((t : Int) + 2) := by omega
  show (x - 0) * (x - 0)
      - ((t : Int) - (↑(2 * t + 2) : Int)) * ((t : Int) - (↑(2 * t + 2) : Int)) ≤ 0
  rw [e1, e2, Int.neg_mul_neg]
  omega

/-- The causal diamond born at the origin and dying at `(2t+2, 0)`. Valid for
    every `t`. -/
def lightDiamond (t : Nat) : CausalDiamond where
  birth := { time := 0, space := 0 }
  death := { time := (↑(2 * t + 2) : Int), space := 0 }
  valid := by
    refine ⟨?_, ?_⟩
    · exact InformationLightCone.cell_in_causal_cone (2 * t + 2) 0 (by omega)
    · rw [decide_eq_true_iff]; show (0 : Int) < (↑(2 * t + 2) : Int); omega

/-- **Integration theorem.** Every subluminal event `(t, x)` with `|x| ≤ t` is
    contained in `lightDiamond t`. Light-theorem events live inside genuine
    `CausalDiamond`s — the objects the kernel forks, races, and folds. -/
theorem subluminal_in_lightDiamond (t : Nat) (x : Int) (h : x.natAbs ≤ t) :
    contains (lightDiamond t) { time := (t : Int), space := x } = true := by
  unfold contains lightDiamond
  have hfut := InformationLightCone.cell_in_causal_cone t x h
  have hpast := subluminal_in_past_cone t x h
  simp only [hfut, hpast, Bool.and_self]

/-- **Certified runtimes inhabit causal diamonds.** A 100%-certified (computable)
    runtime's sample at input `n` is contained in
    `lightDiamond (ackermannCeiling n)`: computation lives inside the kernel's
    causal geometry. -/
theorem certified_runtime_in_diamond (T : Runtime) (n : Nat)
    (hcert : IsKPercentCertified T 100) :
    contains (lightDiamond (ackermannCeiling n))
      { time := (ackermannCeiling n : Int), space := (T n : Int) } = true := by
  have hle : T n ≤ ackermannCeiling n := (cert100_iff T).mp hcert n
  apply subluminal_in_lightDiamond
  omega

/-! ## `lightDiamond` and the kernel's width / sliver / race machinery -/

/-- The time width of `lightDiamond t` is `2t+2` — the refinement budget. -/
theorem timeWidth_lightDiamond (t : Nat) : timeWidth (lightDiamond t) = 2 * t + 2 := by
  simp only [timeWidth, lightDiamond]
  omega

/-- `lightDiamond t` is never a sliver (its width is at least 2). -/
theorem lightDiamond_not_sliver (t : Nat) : isSliver (lightDiamond t) = false := by
  show decide (timeWidth (lightDiamond t) ≤ 1) = false
  rw [timeWidth_lightDiamond]
  exact decide_eq_false (by omega)

/-- **`race` selects the narrower light diamond.** Racing two light diamonds to
    the sliver threshold, the kernel keeps the one with the smaller budget:
    its width is `2·min(s,t)+2`. The light-theorem diamonds compose correctly
    with the kernel's `race`. -/
theorem race_lightDiamond (s t : Nat) :
    timeWidth (race (lightDiamond s) (lightDiamond t)) = 2 * (min s t) + 2 := by
  unfold race
  rw [timeWidth_lightDiamond, timeWidth_lightDiamond]
  by_cases h : 2 * s + 2 ≤ 2 * t + 2
  · rw [if_pos h, timeWidth_lightDiamond]; omega
  · rw [if_neg h, timeWidth_lightDiamond]; omega

end CausalDiamondBridge
