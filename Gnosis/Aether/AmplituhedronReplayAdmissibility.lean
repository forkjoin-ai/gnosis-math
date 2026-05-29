import Init
import Gnosis.QualityMarginCacheAdmissibility

/-!
# Amplituhedron replay admissibility (Rustic Church, Init-only)

This module discharges the **BOUNDED-soundness half** of the
`timeless_isomorphism` covenant that the Death #2 amplituhedron cache
(`open-source/gnosis/distributed-inference/src/amplituhedron.rs`) owes its
header `// COVENANT:` comments. That cache freezes a post-prefill *volume*
(tail residual + KV slab) keyed by `(prefix_hash, prefix_len, layer_lo,
layer_hi)` and re-serves it on a matching prefix, skipping prefill. The
runtime currently admits ONLY exact-hash hits (`tau = 0`, the corner already
shipped). This module certifies the strictly larger admissible region:
**approximate near-prefix replay is provably safe when the frozen-vs-live
prefix divergence is bounded below half the runner-up margin.**

## The bridge rule (what stays outside the theorem)

The served volume's FLOAT numerics — residual vectors, KV slabs, the actual
logit reconstruction — stay OUTSIDE the theorem. They enter only through one
Int-scaled quantity: `tau`, the sup-norm divergence of the served-volume tail
logits `L'` from the true-recompute logits `L`. This is the same
quantize-then-decide bridge as `QualityMarginCacheAdmissibility`: the argmax
decision is scale-invariant, so the half-margin bound is written scale-free as
`2 * tau ≤ gamma`.

## The theorem in one line

If the served tail logits `L'` satisfy `SupNormBelow L L' tau` and the true
logits `L` have a strict argmax `istar` with runner-up margin `gamma`, then the
replayed serve predicts the **same next token** as a full re-execute EXACTLY
WHEN `2 * tau ≤ gamma`. This is a thin re-instantiation of
`QualityMarginCacheAdmissibility.cache_hit_admissible` — the linear-margin
algebra is NOT re-proved here, it is reused wholesale.

## The three regimes (corner / safe band / corruptor)

* `tau = 0` — exact-hash replay. Already shipped; trivially inside the band.
* `0 < 2 * tau ≤ gamma` — approximate near-prefix replay. The win this module
  proves: a frozen volume whose live prefix has drifted by less than half the
  margin is a sound replacement (`replay_admissible`).
* `2 * tau > gamma` — the **amplituhedron-replay corruptor**. The served
  argmax can flip while the cache reports a hit
  (`replay_can_flip_when_divergence_exceeds_half_margin`). Beyond the band a
  replay must **miss, not lie**.

Init-only per `RUSTIC_CHURCH.md`: `import Init` + the sibling gnosis module
only; no Mathlib, no `omega`, no `simp`/`decide` on open-variable goals.
`decide` appears only on CLOSED goals (literal `Fin n` vectors).
-/

open Gnosis.QualityMarginCacheAdmissibility

namespace Gnosis
namespace Aether
namespace AmplituhedronReplayAdmissibility

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The Death #2 cache key (mirror of FiveDeathsCompositionOrthogonality)
-- ═══════════════════════════════════════════════════════════════════════

/-- Death #2 amplituhedron volume-cache key, mirroring
    `FiveDeathsCompositionOrthogonality.AmplituhedronKey` and the runtime
    `(prefix_hash, prefix_len, layer_lo, layer_hi)` of
    `amplituhedron.rs:capture` / `wasm_bindings.rs:529`. The certificate
    speaks the cache's key vocabulary so the bounded-soundness result is
    attached to the exact lookup that serves the frozen volume. -/
structure AmplituhedronKey where
  prefix_hash : Nat
  prefix_len : Nat
  layer_lo : Nat
  layer_hi : Nat
  deriving Repr, DecidableEq

/-- The runtime replay gate fires on an *exact* key match (current shipped
    behaviour). Modeled as structural equality of the 4-Nat tuple. -/
def keyMatches (a b : AmplituhedronKey) : Bool :=
  Nat.beq a.prefix_hash b.prefix_hash &&
  Nat.beq a.prefix_len b.prefix_len &&
  Nat.beq a.layer_lo b.layer_lo &&
  Nat.beq a.layer_hi b.layer_hi

/-- A key matches itself: the trivial reflexivity that ties `keyMatches` to
    the runtime "same prefix, same layer range" hit condition. -/
theorem keyMatches_refl (k : AmplituhedronKey) : keyMatches k k = true := by
  unfold keyMatches
  have hh : Nat.beq k.prefix_hash k.prefix_hash = true := Nat.beq_refl k.prefix_hash
  have hl : Nat.beq k.prefix_len k.prefix_len = true := Nat.beq_refl k.prefix_len
  have hlo : Nat.beq k.layer_lo k.layer_lo = true := Nat.beq_refl k.layer_lo
  have hhi : Nat.beq k.layer_hi k.layer_hi = true := Nat.beq_refl k.layer_hi
  rw [hh, hl, hlo, hhi]
  rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Bounded replay admissibility (thin reuse of the imported core)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Bounded replay admissibility (the τ rule for amplituhedron serves).** Given
the served-volume tail logits `L'` are within sup-norm `tau` of the true
recompute logits `L`, and `L` has a strict argmax `istar` with runner-up margin
`gamma` satisfying `2 * tau ≤ gamma`, the replayed serve is admissible: it
predicts the same next token as a full re-execute.

This is a DIRECT call to the imported
`QualityMarginCacheAdmissibility.cache_hit_admissible` — the entire
linear-margin algebra (`L' j < L j + tau ≤ L istar - tau < L' istar`) is reused,
not re-proved. The amplituhedron contribution is solely the bridge reading: for
this cache, `L'` is the served frozen-volume tail and `tau` is the frozen-vs-live
prefix divergence. -/
theorem replay_admissible {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hstar : IsStrictArgmax L istar)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    Admissible L L' :=
  cache_hit_admissible L L' istar gamma tau hstar hmargin hbound htau

/--
**Gate equivalence on the replayed serve.** A wrapper over the imported
`predicted_token_preserved`: under the bounded-replay premises, *any* strict
argmax of the served tail logits equals the true argmax `istar`. So the PARIS
probe over the replayed volume returns exactly the next token a full re-execute
would — the gate cannot tell the frozen serve from the live computation. -/
theorem replay_token_preserved {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    ∀ i', IsStrictArgmax L' i' → i' = istar :=
  predicted_token_preserved L L' istar gamma tau hmargin hbound htau

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The corruptor antitheorem (the bound is tight)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Sharpness: unbounded replay flips the token (the amplituhedron-replay
corruptor).** The half-margin band is tight. Reusing the imported `Fin 2`
witnesses `flipL` / `flipL'`: the true tail logits `flipL` win token 0 with
margin `gamma = 2`, and the served frozen volume `flipL'` is within sup-norm
`tau = 3` of them — but with the bound violated (`2 * tau = 6 > 2 = gamma`) the
served argmax has flipped to token 1. The cache "reports a hit" (a key match
exists, modeled here by `keyMatches_refl` on any key), yet the served token is
wrong: a replay that lies instead of missing. This is the corruptor signature
the runtime's exact-hash-only policy avoids and that the safe band excludes.

Each conjunct is a CLOSED goal (literal `Fin 2` vectors), so `decide` is
admitted by the Rustic Church contract — kernel-checked, not an open-goal
arithmetic tactic. Mirrors
`QualityMarginCacheAdmissibility.argmax_can_flip_when_bound_violated`. -/
theorem replay_can_flip_when_divergence_exceeds_half_margin
    (k : AmplituhedronKey) :
    -- the cache reports a hit (exact key match)
    keyMatches k k = true ∧
    -- true tail logits: token 0 wins with margin gamma = 2
    IsStrictArgmax flipL ⟨0, by decide⟩ ∧
    MarginAtLeast flipL ⟨0, by decide⟩ 2 ∧
    (0 : Int) < 2 ∧
    -- served frozen volume is within sup-norm tau = 3 of the true tail
    SupNormBelow flipL flipL' 3 ∧
    -- but the half-margin bound is violated: 2 * tau = 6 > 2 = gamma
    ¬ (2 * (3 : Int) ≤ 2) ∧
    -- so the served argmax is NOT token 0: the replay flipped the token
    ¬ IsStrictArgmax flipL' ⟨0, by decide⟩ := by
  refine ⟨keyMatches_refl k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    match j with
    | ⟨0, _⟩ => exact absurd rfl hj
    | ⟨1, _⟩ => show (0 : Int) < 2; decide
  · intro j hj
    match j with
    | ⟨0, _⟩ => exact absurd rfl hj
    | ⟨1, _⟩ => show (0 : Int) + 2 ≤ 2; decide
  · decide
  · intro k
    match k with
    | ⟨0, _⟩ => exact ⟨by show (-3 : Int) < 2 - 0; decide, by show (2 : Int) - 0 < 3; decide⟩
    | ⟨1, _⟩ => exact ⟨by show (-3 : Int) < 0 - 2; decide, by show (0 : Int) - 2 < 3; decide⟩
  · decide
  · intro hcontra
    have hgt := hcontra ⟨1, by decide⟩ (by decide)
    exact absurd hgt (by show ¬ ((2 : Int) < 0); decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Concrete worked replay example (a 3-token near-prefix serve)
-- ═══════════════════════════════════════════════════════════════════════

/-! A station froze a volume for some prefix; the live prefix has drifted
slightly. True recompute tail logits `[5, 1, 0]`: token 0 wins with runner-up
margin `gamma = 4`. The served frozen volume reconstructs `[6, 2, 1]` — every
tail coordinate diverged by `+1`, so sup-norm error `< tau = 2`, and
`2 * tau = 4 ≤ 4 = gamma`. The certificate routes the serve through
`replay_admissible`, certifying the near-prefix replay is served safely. -/

/-- A concrete Death #2 key for the worked replay (values immaterial; the cert
    only needs a key to speak the cache's vocabulary). -/
def exKey : AmplituhedronKey :=
  { prefix_hash := 196884, prefix_len := 7, layer_lo := 0, layer_hi := 11 }

/-- True recompute tail logits of the worked replay. -/
def exReplayL : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Served frozen-volume tail logits of the worked replay (each `+1` drift). -/
def exReplayL' : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Token 0 is the strict argmax of the true recompute tail. -/
theorem exReplay_true_argmax : IsStrictArgmax exReplayL ⟨0, by decide⟩ := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) < 5; decide
  | ⟨2, _⟩ => show (0 : Int) < 5; decide

/-- The true recompute tail has runner-up margin `gamma = 4` at token 0. -/
theorem exReplay_margin : MarginAtLeast exReplayL ⟨0, by decide⟩ 4 := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) + 4 ≤ 5; decide
  | ⟨2, _⟩ => show (0 : Int) + 4 ≤ 5; decide

/-- The served frozen volume is within sup-norm `tau = 2` of the true tail. -/
theorem exReplay_bound : SupNormBelow exReplayL exReplayL' 2 := by
  intro k
  match k with
  | ⟨0, _⟩ => exact ⟨by show (-2 : Int) < 5 - 6; decide, by show (5 : Int) - 6 < 2; decide⟩
  | ⟨1, _⟩ => exact ⟨by show (-2 : Int) < 1 - 2; decide, by show (1 : Int) - 2 < 2; decide⟩
  | ⟨2, _⟩ => exact ⟨by show (-2 : Int) < 0 - 1; decide, by show (0 : Int) - 1 < 2; decide⟩

/-- **Worked near-prefix replay is admissible.** A key match exists
    (`keyMatches_refl exKey`) and the bounded-divergence serve predicts the same
    next token. Routes through `replay_admissible`, so the worked example is a
    live carrier of the general bound, not a standalone calculation. -/
theorem exReplay_admissible :
    keyMatches exKey exKey = true ∧ Admissible exReplayL exReplayL' :=
  ⟨keyMatches_refl exKey,
   replay_admissible exReplayL exReplayL' ⟨0, by decide⟩ 4 2
     exReplay_true_argmax exReplay_margin exReplay_bound (by decide)⟩

end AmplituhedronReplayAdmissibility
end Aether
end Gnosis
