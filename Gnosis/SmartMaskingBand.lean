import Gnosis.KKMLemmaShadow

/-!
# Gnosis.SmartMaskingBand

Bounded formal shadow for language/phoneme/token masking.

The runtime idea is deliberately conservative: a query induces an admissible
token band, and decode only walks inside that band unless a caller asks for the
unmasked universe. The proof obligation is not "the model is smarter"; it is
"the band never increases the search space, and a strict band reduces the
discrete work budget."
-/

namespace Gnosis
namespace SmartMaskingBand

open KKMLemmaShadow

/-- Runtime token admissibility band. `true` means the token remains eligible. -/
abbrev TokenBand := Mask

/-- Discrete work budget: number of admissible tokens in the band. -/
def activeCount : TokenBand → Nat
  | [] => 0
  | b :: t => (if b then 1 else 0) + activeCount t

/-- Intersect a query band with a language/phoneme band. -/
def bandAnd : TokenBand → TokenBand → TokenBand :=
  maskAnd

/-- Full unmasked band of fixed finite size. -/
def fullBand : Nat → TokenBand
  | 0 => []
  | n + 1 => true :: fullBand n

/-- A mask is strict when it removes at least one token. -/
def hasSuppressedToken : TokenBand → Bool
  | [] => false
  | b :: t => (!b) || hasSuppressedToken t

theorem activeCount_fullBand_8 :
    activeCount (fullBand 8) = 8 := by
  native_decide

theorem activeCount_language_band_sample :
    activeCount [true, false, true, true, false, false, true, false] = 4 := by
  native_decide

theorem bandAnd_sample_never_adds :
    activeCount (bandAnd
      [true, true, false, true, false, true, false, true]
      [true, false, true, true, false, false, true, true]) = 3 := by
  native_decide

theorem strict_band_reduces_sample :
    hasSuppressedToken [true, false, true, true, false, false, true, false] = true ∧
    activeCount [true, false, true, true, false, false, true, false] <
      activeCount (fullBand 8) := by
  native_decide

/-- Runtime promotion contract: before enabling a hard mask by default, provide
a finite certificate that its active set is no larger than the full universe and
that quality evidence was collected outside a Goodhart single-prompt target. -/
structure SmartMaskEvidence where
  vocabSize : Nat
  activeTokens : Nat
  qualityPrompts : Nat
  parisPromptIncluded : Bool
  nonParisPrompts : Nat
  deriving Repr

def EligibleForDefaultMask (evidence : SmartMaskEvidence) : Prop :=
  evidence.activeTokens ≤ evidence.vocabSize ∧
  evidence.qualityPrompts ≥ 4 ∧
  evidence.parisPromptIncluded = true ∧
  evidence.nonParisPrompts ≥ 3

theorem default_mask_review_requires_non_paris_prompts
    (evidence : SmartMaskEvidence)
    (h : EligibleForDefaultMask evidence) :
    evidence.nonParisPrompts ≥ 3 :=
  h.right.right.right

theorem sample_default_mask_evidence :
    EligibleForDefaultMask
      { vocabSize := 16, activeTokens := 6, qualityPrompts := 5,
        parisPromptIncluded := true, nonParisPrompts := 4 } := by
  unfold EligibleForDefaultMask
  exact ⟨by native_decide, by native_decide, rfl, by native_decide⟩

end SmartMaskingBand
end Gnosis
