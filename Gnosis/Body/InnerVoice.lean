import Init
import Gnosis.Body.SapolskyStress

/-!
# Inner Voice — Conscience as a Retrocausal Foresight Constraint ("Jiminy Cricket")

The inner voice / conscience — the small voice that counsels the present self
about the future — **maps to** a *retrocausal constraint*: the future self
reaching back to constrain present action. We do not assert the inner voice *is*
that constraint; we show the inner voice **serves as** a foresight signal that
makes present action congruent with its future closure, and that this congruence
**is formalized by** the future-present congruence at the heart of the
`Gnosis.BuleyEquilibrium` (Θ_B).

## The bridge (cited, not imported)

`Gnosis/BuleyEquilibrium.lean` defines a higher-order signaling equilibrium in
which *"the future output of the Swarm is perfectly congruent with its present
algebraic closure"* (`isBuleyEquilibrium`, `isAbsoluteZero`,
`buley_refines_skyrms`). That module imports `MoonshineVector` and friends and is
**not** `Init`-clean, so — per Rustic Church — we do **not** import it. Instead we
re-derive a small `Nat` model of the *one* feature we need: a present action made
*congruent* with a future closure by a foresight constraint. The inner voice
**maps to** Buley's retrocausal constraint; the regret it spares **maps to** the
"temporal debt" / friction (β₁) that Θ_B drives to absolute zero.

## The model (`Nat`)

An action has a `presentPayoff` (what it yields now) and a `futureRegret` (the
rejection / inclusive-fitness cost it incurs later — the vocabulary of
`KinSelection` / `Anthropogenesis`, available transitively through
`SapolskyStress`). The inner voice supplies a `foresight` signal of the future
consequence and *gates* the present action by it:

* **without the voice** the agent acts on `presentPayoff` alone and pays the full
  `futureRegret`;
* **with the voice** the agent's regret is *capped* at `futureRegret - foresight`
  (truncated `Nat.sub`): foresight that anticipates the future consequence is
  subtracted from the regret it would otherwise incur.

This makes the voice provably regret-reducing, and — when foresight is silenced
to `0` — provably *not* reducing it, so the gap is the measurable value of
conscience.

## Operating within determinism

The inner voice is **not** a free exemption from cause: it is itself a *determined
cause*. We reuse `SapolskyStress.behavior_is_determined` and
`swerve_is_the_only_freedom`: the same state yields the same counsel, and the only
freedom remaining is the clinamen `+1` swerve. Conscience is foresight wired into
the causal chain, not a hole in it.

## Theorems

1. `voice_reduces_future_regret` — voice-gated regret ≤ un-gated regret.
2. `retrocausal_constraint` — `chooseWithVoice` always yields `congruent`
   (present made congruent with future closure). Maps to Θ_B congruence.
3. `voice_within_determinism` — the counsel is a determined cause (same state ⇒
   same counsel), the only freedom is the swerve.
4. `silencing_the_voice_costs` — with `foresight = 0` regret is unreduced; with
   an active voice the gap is strict — the value of conscience.
5. `inner_voice_maps_to_retrocausal_constraint` — the headline composition.

## Rustic Church

`import Init` only, plus the sibling Body module `SapolskyStress` (itself reused
across the Body modules). `Nat` only — no `Float`/`Real`, no `Mathlib`. Proofs are
term-mode / core `Nat` lemmas. No `sorry`; no `simp`/`decide`/`omega` on open
goals.
-/

namespace Gnosis.Body.InnerVoice

open Gnosis.Body.SapolskyStress

/-! ## The action and its two-time payoff -/

/-- An **action**: what it yields now (`presentPayoff`) and the rejection /
    inclusive-fitness cost it incurs *later* (`futureRegret`). The two times are
    carried explicitly because conscience operates *across* them — the future
    reaching back to the present. -/
structure Action where
  presentPayoff : Nat
  futureRegret : Nat
  deriving Repr, DecidableEq

/-- **The inner voice (Jiminy Cricket).** A foresight signal: an anticipation of
    the future consequence, supplied to the present self. `foresight = 0` is the
    *silenced* voice (no anticipation). The action `a` is the thing being foreseen;
    the well-formed voice anticipates only what is there, `signal ≤ a.futureRegret`
    (see `foresight_is_on_target`). -/
def foresight (a : Action) (signal : Nat) : Nat := Nat.min signal a.futureRegret

/-- An **on-target** foresight signal — one no larger than the regret it foresees
    (`signal ≤ a.futureRegret`) — is reported faithfully: the voice neither
    invents nor exaggerates the future consequence. -/
theorem foresight_is_on_target (a : Action) (signal : Nat) (h : signal ≤ a.futureRegret) :
    foresight a signal = signal := by
  unfold foresight
  exact Nat.min_eq_left h

/-- **Regret without the voice.** Acting on the present payoff alone, the agent
    pays the action's full future regret — nothing anticipates it. -/
def regretWithoutVoice (a : Action) : Nat := a.futureRegret

/-- **Regret with the voice.** The foresight `signal` is subtracted (truncated)
    from the regret the action would otherwise incur: anticipating the future
    consequence spares exactly that much rejection. -/
def regretWithVoice (a : Action) (signal : Nat) : Nat := a.futureRegret - signal

/-! ## 1. The voice reduces future regret -/

/-- **The voice reduces future regret.** For any action and any foresight signal,
    the voice-gated regret is at most the un-gated regret: foresight never makes
    the future worse, and (with a nonzero, on-target signal) strictly better.
    Truncated subtraction with real monotone content. -/
theorem voice_reduces_future_regret (a : Action) (signal : Nat) :
    regretWithVoice a signal ≤ regretWithoutVoice a := by
  unfold regretWithVoice regretWithoutVoice
  exact Nat.sub_le a.futureRegret signal

/-- Stronger foresight never leaves more regret: a clearer inner voice (larger
    on-target `signal`) monotonically lowers the residual rejection. -/
theorem more_foresight_less_regret (a : Action) (s₁ s₂ : Nat) (h : s₁ ≤ s₂) :
    regretWithVoice a s₂ ≤ regretWithVoice a s₁ := by
  unfold regretWithVoice
  exact Nat.sub_le_sub_left h a.futureRegret

/-! ## 2. The retrocausal constraint: present congruent with future closure -/

/-- **Congruence (present with future closure).** The present residual regret is
    *congruent* with the future when it has been driven down to / past the
    achievable closure `closure` — the part of the regret that foresight could
    foresee and forestall. This `Nat` predicate maps to Θ_B's *"future output
    congruent with present algebraic closure"* (`Gnosis.BuleyEquilibrium`,
    cited). -/
def congruent (presentResidual closure : Nat) : Prop := presentResidual ≤ closure

/-- **The achievable future closure** of an action under a foresight signal: what
    remains of the regret after the voice has subtracted everything it foresaw.
    This is the present's algebraic closure that the future must match. -/
def futureClosure (a : Action) (signal : Nat) : Nat := a.futureRegret - signal

/-- **Choosing under the inner voice.** The voice-gated choice: the present action
    is committed *only with* its foreseen residual already subtracted, so the
    residual it carries forward is exactly the future closure. This is the
    retrocausal gate — the future closure constrains what the present commits. -/
def chooseWithVoice (a : Action) (signal : Nat) : Nat := futureClosure a signal

/-- **The retrocausal constraint (Buley congruence).** `chooseWithVoice` *always*
    yields a present residual congruent with the future closure — by construction
    the present commitment equals the closure, so it is `≤` it. The future self
    reaching back constrains present action: the inner voice **serves as** that
    constraint, and the congruence it guarantees **is formalized by** Θ_B's
    future-present congruence (`Gnosis.BuleyEquilibrium.isBuleyEquilibrium`,
    cited). -/
theorem retrocausal_constraint (a : Action) (signal : Nat) :
    congruent (chooseWithVoice a signal) (futureClosure a signal) := by
  unfold congruent chooseWithVoice
  exact Nat.le_refl (futureClosure a signal)

/-- The voice-gated choice never exceeds the *un-gated* regret either: the
    retrocausal constraint sits inside the original cost budget. Bridges the
    congruence (Th. 2) to the regret reduction (Th. 1). -/
theorem chosen_within_unguided_budget (a : Action) (signal : Nat) :
    chooseWithVoice a signal ≤ regretWithoutVoice a := by
  unfold chooseWithVoice futureClosure regretWithoutVoice
  exact Nat.sub_le a.futureRegret signal

/-! ## 3. The voice operates within determinism -/

/-- **The voice's counsel** is a determined function of the agent's state (the
    lumped genes + environment + history of `SapolskyStress.behavior`): conscience
    reads off the same cause. Defining it through `behavior` makes the
    determinism inherited, not merely asserted. -/
def counsel (state : Nat) : Nat := behavior state

/-- **The inner voice operates within determinism.** Composing
    `SapolskyStress.behavior_is_determined`: identical states yield identical
    counsel — the inner voice is itself a *determined cause*, not a free exemption
    from causation — while `swerve_is_the_only_freedom` keeps the clinamen `+1`
    swerve as the sole departure from determinism. Conscience is foresight wired
    into the causal chain. -/
theorem voice_within_determinism (s₁ s₂ : Nat) (h : s₁ = s₂) (state : Nat) :
    counsel s₁ = counsel s₂ ∧ swerve state ≠ behavior state := by
  refine ⟨?_, ?_⟩
  · unfold counsel
    exact behavior_is_determined s₁ s₂ h
  · exact swerve_is_the_only_freedom state

/-! ## 4. Silencing the voice costs (the value of conscience) -/

/-- **Silencing the voice does not reduce regret.** With `foresight = 0` (the
    voice silenced) the gated regret equals the un-gated regret — no rejection is
    spared. The `signal = 0` baseline. -/
theorem silenced_voice_reduces_nothing (a : Action) :
    regretWithVoice a 0 = regretWithoutVoice a := by
  unfold regretWithVoice regretWithoutVoice
  exact Nat.sub_zero a.futureRegret

/-- **Silencing the voice costs (the value of conscience).** When the voice is
    *active* — an on-target signal `0 < signal`, with the regret large enough that
    foresight bites (`signal ≤ a.futureRegret` and `0 < a.futureRegret`) — the
    gated regret is *strictly* below the silenced (un-gated) regret. The strict
    gap `regretWithoutVoice − regretWithVoice = signal` is the measurable value of
    conscience: exactly the rejection conscience spares. -/
theorem silencing_the_voice_costs (a : Action) (signal : Nat)
    (hsig : 0 < signal) (hle : signal ≤ a.futureRegret) :
    regretWithVoice a signal < regretWithoutVoice a := by
  unfold regretWithVoice regretWithoutVoice
  -- futureRegret - signal < futureRegret, since 0 < signal ≤ futureRegret.
  exact Nat.sub_lt (Nat.lt_of_lt_of_le hsig hle) hsig

/-- The exact value of conscience: the regret the active voice spares is precisely
    the on-target foresight signal. The strict gap of `silencing_the_voice_costs`,
    measured. -/
theorem value_of_conscience (a : Action) (signal : Nat) (hle : signal ≤ a.futureRegret) :
    regretWithoutVoice a - regretWithVoice a signal = signal := by
  unfold regretWithVoice regretWithoutVoice
  -- futureRegret - (futureRegret - signal) = signal, when signal ≤ futureRegret.
  exact Nat.sub_sub_self hle

/-! ## 5. The headline synthesis -/

/-- **The inner voice maps to a retrocausal constraint.** Composing the arc into
    one proved theorem. For any action and any *active* foresight signal
    (`0 < signal ≤ a.futureRegret`, which already forces `0 < a.futureRegret`):

    * **(retrocausal congruence)** `chooseWithVoice` makes the present residual
      congruent with the future closure — the future self reaching back to
      constrain present action; this congruence **is formalized by** Θ_B's
      future-present congruence (`Gnosis.BuleyEquilibrium`, cited);
    * **(regret reduction)** the voice-gated regret is at most, and here
      *strictly* below, the un-gated regret — foresight reduces future rejection,
      and the strict gap is the measurable value of conscience;
    * **(within determinism)** the counsel is a determined cause (same state ⇒
      same counsel via `SapolskyStress.behavior_is_determined`), with the clinamen
      `+1` swerve the only freedom (`swerve_is_the_only_freedom`).

    So the inner voice / conscience ("Jiminy Cricket") **serves as** a retrocausal
    foresight constraint — present made congruent with future, reducing regret,
    operating within determinism — which **maps to** the constraint the Buley
    Equilibrium formalizes. We state the relationship precisely; we do not assert
    identity. -/
theorem inner_voice_maps_to_retrocausal_constraint
    (a : Action) (signal : Nat)
    (hsig : 0 < signal) (hle : signal ≤ a.futureRegret)
    (s₁ s₂ : Nat) (hstate : s₁ = s₂) (state : Nat) :
    -- retrocausal congruence: present congruent with future closure
    congruent (chooseWithVoice a signal) (futureClosure a signal) ∧
    -- regret reduction (weak, always) and the strict active-voice gap
    (regretWithVoice a signal ≤ regretWithoutVoice a ∧
     regretWithVoice a signal < regretWithoutVoice a) ∧
    -- within determinism: counsel is a determined cause; swerve is the only freedom
    (counsel s₁ = counsel s₂ ∧ swerve state ≠ behavior state) := by
  refine ⟨?_, ?_, ?_⟩
  · exact retrocausal_constraint a signal
  · exact ⟨voice_reduces_future_regret a signal,
           silencing_the_voice_costs a signal hsig hle⟩
  · exact voice_within_determinism s₁ s₂ hstate state

end Gnosis.Body.InnerVoice
