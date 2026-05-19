import Init

/-
  SapphoAttentionCouplet.lean
  ===========================

  Couplet (paraphrase att. Sappho, fragment tradition):

    “To me the most beautiful thing / is whatever one loves.”

  Attention reading: on a carrier `α` of appearances, *love* is modeled as
  an attention predicate `attn : α → Prop` — what one admits into the
  witness band. *Beauty* is not a second, independent chart over all of `α`;
  it is coextensional with that mask. Same structural move as gated
  value flow in `AttentionQKVDecomposition` / standing-wave selectivity in
  `AttentionWavePattern`: the output lives on the support you actually open.

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace SapphoAttentionCouplet

variable {α : Type} (attn : α → Prop)

/-- Love as attention: what one loves is exactly what one admits. -/
abbrev Loves (x : α) : Prop :=
  attn x

/-- Beauty as the attended chart: “most beautiful” is whatever sits in the
    attention fiber — no extra free parameter beyond `attn`. -/
abbrev Beautiful (x : α) : Prop :=
  Loves attn x

/-- The couplet, as a single definitional equality at the level of propositions:
    beauty is attention. -/
theorem beauty_is_attention (x : α) : Beautiful attn x ↔ attn x :=
  Iff.rfl

end SapphoAttentionCouplet
