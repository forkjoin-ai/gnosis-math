import Gnosis.SkyrmsEnergyTax

/-!
# Contrarian Dominant Attention Is Innocent

High attention mass is not the taxable offense. Externality is.

In the Skyrms energy-tax surface, a dominant head that produces useful work,
truth, and diversity while imposing zero routing waste, congestion, failed
attention, and unresolved debt pays only the clinamen floor. A weaker head with
positive harmful externality pays more.
-/

namespace Gnosis
namespace ContrarianDominantAttentionIsInnocent

open Gnosis.SkyrmsEnergyTax

/-- A compact witness for the anti-theorem: dominant attention can be clean,
while a lower-attention head can be harmful. -/
structure DominantAttentionWitness where
  dominant : EnergyNode
  harmful : EnergyNode
  dominant_attention_ge : harmful.attentionValue ≤ dominant.attentionValue
  dominant_externality_zero : externality dominant = 0
  harmful_externality_positive : 0 < externality harmful

/-- Dominance alone does not justify extra tax: a zero-externality dominant head
pays exactly the clinamen floor. -/
theorem dominant_attention_with_zero_externality_pays_floor
    (w : DominantAttentionWitness) :
    skyrmsTax w.dominant = 1 := by
  unfold skyrmsTax
  rw [w.dominant_externality_zero]

/-- The harmful head pays strictly more than the clean dominant head. -/
theorem harmful_externality_tax_exceeds_clean_dominance
    (w : DominantAttentionWitness) :
    skyrmsTax w.dominant < skyrmsTax w.harmful := by
  rw [dominant_attention_with_zero_externality_pays_floor w]
  unfold skyrmsTax
  exact Nat.succ_lt_succ w.harmful_externality_positive

/-- Contrarian summary: the taxable property is harmful externality, not
attention dominance. -/
theorem contrarian_dominant_attention_is_innocent
    (w : DominantAttentionWitness) :
    skyrmsTax w.dominant < skyrmsTax w.harmful ∧
      w.harmful.attentionValue ≤ w.dominant.attentionValue :=
  ⟨harmful_externality_tax_exceeds_clean_dominance w, w.dominant_attention_ge⟩

end ContrarianDominantAttentionIsInnocent
end Gnosis
