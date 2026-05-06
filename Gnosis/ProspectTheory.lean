import Init
import Gnosis.GodFormula
import Gnosis.GoodhartsLaw

/-!
# Prospect theory — unified `Init`-layer package

Reference-dependent **piecewise-linear** subjective value, proved **loss aversion**
(symmetric magnitudes), **EmotionGait** indexing, neutral **π** stub, and the
**God-weight** spine (`goodhart_strict_antitone`, unit marginal, conservation).

Loss-aversion coefficient is **`lam`** (Lean reserves `λ`).

Import this module from witnesses that need **proved** hooks instead of comment-only
story.
-/

namespace Gnosis
namespace ProspectTheory

open Gnosis (godWeight godWeight_ordered_difference godWeight_conservation goodhart_strict_antitone)

/-! ## Deviation and piecewise-linear value -/

def deviation (wealth ref : Nat) : Int :=
  (wealth : Int) - (ref : Int)

def subjectiveLinear (lam : Nat) (wealth ref : Nat) : Int :=
  let d := deviation wealth ref
  if _ : d ≥ 0 then
    d
  else
    - (lam : Int) * Int.ofNat (Int.natAbs d)

theorem subjectiveLinear_five_two (lam : Nat) : subjectiveLinear lam 5 2 = 3 := by
  rfl

theorem subjectiveLinear_five_eight (lam : Nat) :
    subjectiveLinear lam 5 8 = - (lam : Int) * (3 : Int) := by
  rfl

/-! ### Loss aversion (symmetric magnitudes) -/

def gainValue (mag : Nat) : Int :=
  (mag : Int)

def lossDepth (lam mag : Nat) : Int :=
  (lam : Int) * (mag : Int)

theorem loss_aversion_symmetric_pos {lam l : Nat} (hlam : 1 < lam) (hl : 0 < l) :
    lossDepth lam l > gainValue l := by
  unfold lossDepth gainValue
  have hlz : 0 < (l : Int) := Int.natCast_pos.mpr hl
  have hlam₁ : 1 < (lam : Int) := Int.ofNat_lt.mpr hlam
  simpa [Int.one_mul] using Int.mul_lt_mul_of_pos_right hlam₁ hlz

/-! ### Reference dependence -/

theorem reference_shift_valuations_differ (lam : Nat) (hlam : 0 < lam) :
    subjectiveLinear lam 5 2 ≠ subjectiveLinear lam 5 8 := by
  intro heq
  have hL : 0 < subjectiveLinear lam 5 2 := by
    rw [subjectiveLinear_five_two lam]
    decide
  have hR : subjectiveLinear lam 5 8 < 0 := by
    rw [subjectiveLinear_five_eight lam]
    have hp : 0 < (lam : Int) * (3 : Int) :=
      Int.mul_pos (Int.natCast_pos.mpr hlam) (by decide : (0 : Int) < 3)
    rw [Int.neg_mul]
    exact Int.neg_neg_of_pos hp
  rw [heq] at hL
  exact Int.lt_irrefl (0 : Int) (Int.lt_trans hL hR)

/-! ## God-weight spine (strict antitone, unit marginal, conservation) -/

theorem structural_strict_antitone (R v_lo v_hi : Nat)
    (h_lo : v_lo ≤ R) (h_hi : v_hi ≤ R) (h : v_lo < v_hi) :
    godWeight R v_hi < godWeight R v_lo :=
  goodhart_strict_antitone R v_lo v_hi h_lo h_hi h

theorem structural_marginal_unit_drop (R v : Nat) (hv : v < R) :
    godWeight R v - godWeight R (v + 1) = 1 := by
  have v_le : v ≤ R := Nat.le_of_lt hv
  have v1_le : v + 1 ≤ R := Nat.succ_le_of_lt hv
  simpa using
    (godWeight_ordered_difference R v (v + 1) v_le v1_le (Nat.le_succ v))

theorem structural_conservation (R v : Nat) (hv : v ≤ R) : godWeight R v + v = R + 1 :=
  godWeight_conservation R v hv

/-! ## Emotion gait (stand → … → gallop) — discrete scale -/

inductive EmotionGait where
  | stand
  | trot
  | canter
  | gallop
  deriving DecidableEq, Repr

def gaitIndex : EmotionGait → Fin 4
  | .stand => ⟨0, by decide⟩
  | .trot => ⟨1, by decide⟩
  | .canter => ⟨2, by decide⟩
  | .gallop => ⟨3, by decide⟩

theorem gaitIndex_le_three (g : EmotionGait) : (gaitIndex g).val ≤ 3 := by
  cases g <;> decide

/-! ## CPT — neutral probability weight -/

def probabilityWeightId (p : Nat) : Nat := p

theorem probabilityWeightId_id (p : Nat) : probabilityWeightId p = p :=
  rfl

/-! ## Master certificate -/

theorem prospect_theory_kernel_certificate {lam : Nat} (hlam : 1 < lam) (l : Nat) (hl : 0 < l)
    (R v₀ v₁ : Nat) (hR₀ : v₀ ≤ R) (hR₁ : v₁ ≤ R) (hvv : v₀ < v₁) :
    lossDepth lam l > gainValue l ∧
    godWeight R v₁ < godWeight R v₀ ∧
    godWeight R v₀ - godWeight R v₁ = v₁ - v₀ :=
  ⟨loss_aversion_symmetric_pos hlam hl, structural_strict_antitone R v₀ v₁ hR₀ hR₁ hvv,
    godWeight_ordered_difference R v₀ v₁ hR₀ hR₁ (Nat.le_of_lt hvv)⟩

end ProspectTheory
end Gnosis
