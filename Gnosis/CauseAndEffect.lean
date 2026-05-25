/-
  CauseAndEffect.lean
  ===================

  Cause and effect, as a finite carrier. This is the extracted core that the
  clinamen-swerve games were re-deriving piecemeal: the precise sense in which
  "cause and effect are mapped". Two halves, both load-bearing:

    1. COUNTERFACTUAL CAUSATION (difference-making, finitized Lewis): a cause is
       what makes the difference — the effect holds with the cause present and
       fails with it removed. `IsDifferenceMaker`.

    2. THE CAUSE↦EFFECT MAPPING: a sign-preserving bijection from causes to
       effects. Every cause has a unique effect of the same sign, and every
       effect traces to a unique cause. `CausalLaw`.

  The shared `Polarity` axis `{−1, 0, +1}` is the one form under many readings —
  declinamen/clinamen/swerve, decline/abstain/accept, destructive/rest/
  constructive interference, silence/sting/trill, fold/race/fork. The witness law
  (the trill witnesses the sting; no cause, no effect) is Basho's haiku stated as
  a theorem on the canonical law.

  Downstream instances:
    * `Gnosis/RebelHadACause.lean`     — the swerve is a difference-maker for survival.
    * `Gnosis/TritonSwerveGame.lean`   — `resonanceOf` is a CausalLaw `Move ↦ Resonance`.
    * `Gnosis/BashoClinamenTrillWitness.lean` — the trill carries the witness reading.

  Init-only Rustic Church. No Mathlib, no `omega`, no `simp`/`decide` on
  open-variable goals; `decide` only on closed statements.
-/
import Init

namespace GnosisMath
namespace CauseAndEffect

-- ══════════════════════════════════════════════════════════
-- PART I.  COUNTERFACTUAL CAUSATION  (difference-making)
-- ══════════════════════════════════════════════════════════

/-- A cause is a difference-maker (finitized Lewis counterfactual): the effect
    holds when the cause is present (`false` = not removed) and fails when the
    cause is removed (`true`). The `Bool` is the world toggle. -/
def IsDifferenceMaker (effect : Bool → Prop) : Prop :=
  effect false ∧ ¬ effect true

/-- The effect is present in the actual (cause-present) world. -/
theorem effect_present {effect : Bool → Prop} (h : IsDifferenceMaker effect) :
    effect false := h.1

/-- The effect is absent in the counterfactual (cause-removed) world. -/
theorem effect_absent {effect : Bool → Prop} (h : IsDifferenceMaker effect) :
    ¬ effect true := h.2

/-- **The two worlds disagree.** A genuine cause forces the cause-present and
    cause-removed worlds apart: the effect cannot hold equivalently in both.
    This is what distinguishes a cause from a mere correlate. -/
theorem worlds_disagree {effect : Bool → Prop} (h : IsDifferenceMaker effect) :
    ¬ (effect false ↔ effect true) := by
  intro hiff
  exact h.2 (hiff.mp h.1)

-- ══════════════════════════════════════════════════════════
-- PART II.  THE CAUSE↦EFFECT MAPPING  (sign-preserving bijection)
-- ══════════════════════════════════════════════════════════

/-- A causal law mapping causes to effects, each signed in `{−1, 0, +1}`, such
    that the map is sign-preserving and a bijection. This is the precise content
    of "cause and effect are mapped": to each cause a unique effect of the same
    sign, and every effect from a unique cause. -/
structure CausalLaw (Cause Effect : Type) where
  causeSign : Cause → Int
  effectSign : Effect → Int
  effectOf : Cause → Effect
  preserves : ∀ c, effectSign (effectOf c) = causeSign c
  surjective : ∀ e, ∃ c, effectOf c = e
  injective : ∀ c1 c2, effectOf c1 = effectOf c2 → c1 = c2

namespace CausalLaw
variable {Cause Effect : Type}

/-- The effect carries the cause's sign. -/
theorem signed (L : CausalLaw Cause Effect) (c : Cause) :
    L.effectSign (L.effectOf c) = L.causeSign c := L.preserves c

/-- Distinct causes have distinct effects: no two causes collapse onto one effect. -/
theorem distinct_causes_distinct_effects (L : CausalLaw Cause Effect)
    {c1 c2 : Cause} (h : c1 ≠ c2) : L.effectOf c1 ≠ L.effectOf c2 :=
  fun he => h (L.injective c1 c2 he)

/-- No uncaused effect: every effect traces back to a cause. -/
theorem no_uncaused_effect (L : CausalLaw Cause Effect) (e : Effect) :
    ∃ c, L.effectOf c = e := L.surjective e

end CausalLaw

-- ══════════════════════════════════════════════════════════
-- PART III.  THE CANONICAL POLARITY LAW  (and the witness reading)
-- ══════════════════════════════════════════════════════════

/-- The shared polarity axis of cause and effect: `{−1, 0, +1}`. The one pure
    form under many readings (clinamen, verdict, interference, Basho, FRF). -/
inductive Polarity
  | neg    -- −1
  | zero   --  0
  | pos    -- +1
  deriving DecidableEq

def Polarity.sign : Polarity → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- The canonical causal law: every effect inherits its cause's polarity. The
    sharpest statement that cause and effect are mapped — a sign-preserving
    bijection of the polarity axis onto itself. -/
def polarityLaw : CausalLaw Polarity Polarity where
  causeSign := Polarity.sign
  effectSign := Polarity.sign
  effectOf := id
  preserves := fun _ => rfl
  surjective := fun e => ⟨e, rfl⟩
  injective := fun _ _ h => h

/-- **The witness law (Basho).** The positive effect (the trill) occurs iff the
    positive cause (the sting): the trill witnesses the sting. -/
theorem effect_witnesses_cause (c : Polarity) :
    polarityLaw.effectOf c = Polarity.pos ↔ c = Polarity.pos := by
  cases c <;> decide

/-- **No cause, no effect.** Without the positive cause the positive effect
    cannot occur — the contrapositive of the witness law. -/
theorem no_cause_no_effect (c : Polarity) (h : c ≠ Polarity.pos) :
    polarityLaw.effectOf c ≠ Polarity.pos :=
  fun he => h ((effect_witnesses_cause c).mp he)

/-- **Cause and effect are mapped.** Bundled on the canonical law: the mapping is
    sign-preserving and onto, and the positive effect witnesses the positive
    cause. -/
theorem cause_and_effect (c : Polarity) :
    polarityLaw.effectSign (polarityLaw.effectOf c) = polarityLaw.causeSign c ∧
    (∀ e, ∃ c', polarityLaw.effectOf c' = e) ∧
    (polarityLaw.effectOf c = Polarity.pos ↔ c = Polarity.pos) :=
  ⟨polarityLaw.preserves c, polarityLaw.surjective, effect_witnesses_cause c⟩

end CauseAndEffect
end GnosisMath
