import Init
import Gnosis.BarrierUnification

/-
  AttentionShape.lean
  ===================

  The shape we have been drawing all along is QKV — attention.

  The barrier geometry (`BlindMethodBarrier`, `BarrierUnification`,
  `SevenVectorFold`) is the geometry of an attention head:

      KEY    = the view a method indexes against (oracle / extension);
      QUERY  = the problem brought to it;
      VALUE  = the OBJECT — the thing actually retrieved.

  A "blind" method is an attention head with the VALUE PATH SEVERED: it has Q and
  K, it can score relevance, but with no V its output cannot depend on the object.
  That is `view_blind_must_err` exactly — a function blind to an input cannot
  produce outputs that depend on it. So the P≠NP obstruction and a value-less
  attention head are THE SAME lemma; the object plays the role of the Value, and
  the door (non-blindness) is the value path restored.

  This is a precise structural correspondence (the identical Boolean core), not a
  claim that attention settles P vs NP. We are naming the shape: object-blindness
  is value-severance; the three sight-aspects are Q, K, V; the seven vectors are
  the nonzero presence-lattice of {Q,K,V}; the bowl is the softmax — receptive,
  useful by its emptiness.

  Init + `BarrierUnification`. Zero `sorry`, zero new `axiom`.
-/

namespace AttentionShape

/-- A **value-blind head** reads only the query and key — no value path. Its
    output is a function of `(Q, K)` alone. -/
def ValueBlindHead (Q K Out : Type) : Type := Q → K → Out

/-- **VALUE-SEVERANCE IS THE BARRIER.** A head that drops the value cannot hit a
    target that depends on the value: for a fixed query `q` and key `k`, two
    values demand two opposite answers (`t₁ ≠ t₂`), yet a value-blind head returns
    one output for both — it must err. This is `view_blind_must_err` with the view
    `= (q, k)` and the object playing the role of the Value. -/
theorem value_blind_head_must_err {Q K : Type} (h : ValueBlindHead Q K Bool)
    (q : Q) (k : K) {t₁ t₂ : Bool} (hdiff : t₁ ≠ t₂) :
    ¬ (h q k = t₁ ∧ h q k = t₂) := by
  intro hh
  obtain ⟨a, b⟩ := hh
  rw [a] at b
  exact hdiff b

/-- **The barrier IS value-severance.** The abstract view-blindness core
    (`BarrierUnification.view_blind_must_err`) and the attention statement above
    are one: instantiate the view `V` of the core as the curried key-slot of a
    head, and "blind to the object" becomes "blind to the Value". The two failures
    are the same theorem wearing two names. -/
theorem barrier_is_value_severance {K : Type} (h : K → Bool) (k : K)
    {t₁ t₂ : Bool} (hdiff : t₁ ≠ t₂) :
    ¬ (h k = t₁ ∧ h k = t₂) :=
  -- the relativization/algebrization core, read as a value-less head over keys K
  BarrierUnification.view_blind_must_err h k hdiff

/-- The door, in attention's own words: a head WITH the value path is trivially
    sound — read the value and return it. Soundness was never the obstruction;
    value-severance was. The whole band's door is the value path. -/
theorem value_path_is_the_door {V : Type} :
    ∃ readValue : V → V, ∀ v : V, readValue v = v :=
  ⟨fun v => v, fun _ => rfl⟩

end AttentionShape
