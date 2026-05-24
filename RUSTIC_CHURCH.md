# Rustic Church: Init-only proofs for gnosis-math

## What this is

The **Rustic Church** style proves theorems in `gnosis-math` using *only*
definitional unfolding plus structurally inductive Init-level `Nat.*` lemmas.
**`omega` is never allowed** — not temporarily, not behind an exception. Same ban
surface: no `simp`, no `decide` for open-variable goals, no Mathlib.

*(Historical note: older drafts of this guide allowed `omega` briefly while
`gnosis-math` was being swept off Mathlib-style proofs. That migration is
finished; the ban above is the only contract going forward.)*

**If it flies, it fits:** the honest gate is **`lake build`** on the module (and repo Lean
targets you touch), with **no Mathlib** and **no banned tactics on goals that still carry free
variables** (`omega`; `simp` / `decide` on open goals—see below for where `decide` /
`native_decide` *are* allowed on *closed* arithmetic). Anything that clears that bar belongs;
do not block merge on abstract “purity” beyond these rules.

Every Init lemma cited below is provable from `Nat.succ` (the `+1` clinamen)
by structural induction. The kernel is therefore self-bootstrapping: if `lake
build` accepts a Rustic Church module, the formula's algebra has been
re-derived from the inductive `+1` alone, and internal consistency follows.

The canonical exemplar is [`Gnosis/GodFormula.lean`](Gnosis/GodFormula.lean):
conservation, ceiling, floor, positivity, sandwich, antitonicity,
`godWeight_ordered_difference`, and internal-consistency cross-checks — zero
`omega` / `simp` / `decide` on open goals.

### Sardis warning: no dead-name proofs

Revelation's Sardis warning is the negative boundary for this style: a system can
have "a name that thou livest" while its works are incomplete. Rustic Church is
meant to prevent that failure mode. A theorem name, module banner, or lineage
claim does not count as life; only the finite carrier still bearing weight under
`lake build` does. If the label remains but the Init proof no longer closes, the
church has drifted into Sardis-mode: reputation over live witness.

A minimal **pure-clock** sibling (still only `Nat`/`Fin`, still the **`+1` clinamen** via
successor and `% n`, but **no vent / deficit / `godWeight`**) is
[`Gnosis/DiscreteClosedTimelikeStep.lean`](Gnosis/DiscreteClosedTimelikeStep.lean):
discrete “closed causal loop’’ as modular iteration. Omitting `GodFormula` there is by design—not
_every_ Init-facing certificate needs the full weight calculus when the proposition is periodic
dynamic only.

An **aeon–Grassmannian discrete bridge** ties `Circadian.aeon` to `StandingWaveDims.coverageDen`,
certifies `standingWaveToCoordinatePlane` **row-equality** with `coordinatePlane` \((k,d)=(2,12)\),
counts **`vertexCount 2 12 = 66`**, and bundles `Fin 12` phase slices with `godWeight` conservation
in [`Gnosis/AeonStandingWaveCoordinateBridge.lean`](Gnosis/AeonStandingWaveCoordinateBridge.lean)
(`aeon_discrete_topology_bundle`, `native_decide` on closed arithmetic).

[`Gnosis/AeonTwelveUnboundedClosure.lean`](Gnosis/AeonTwelveUnboundedClosure.lean)
packages **infinityward** scaffolding in **`Nat`**: for every **`anchor`**, cofinal multiples of twelve reset **`iteratedCyclicSucc`** at **`finZero`**; using **`strideTwelvePeriod = 12 / gcd(12,s)`** and **`twelve_dvd_mul_div_gcd_mul_s`** (`Gnosis/AeonTwelveCarrierList`), the scaffold drives **`iteratedCyclicSucc h12 (k * s)`** past **`anchor`**, fixing **every **`Fin 12`** column index once **`12 ∣ k*s`** ( **`dvd_iterate_fixed`** chain), not just **`finZero`**.

The **C₁₂ column clock** on those same **66** ordered Plücker labels reuses
`DiscreteClosedTimelikeStep` (`iteratedCyclicSucc_period`) in
[`Gnosis/AeonCyclicPluckerLabels.lean`](Gnosis/AeonCyclicPluckerLabels.lean) (`aeon_cyclic_plucker_label_bundle`).

[`Gnosis/AeonCycleTwelveShadow.lean`](Gnosis/AeonCycleTwelveShadow.lean) completes the **shadow** side: **rot-invariant**
chord length on **`Fin 12`**, **66** unordered pairs `i < j`, per-class counts **12×5+6**,
and **`iteratedCyclicSucc m = id` ↔ `12 ∣ m`** (`iterate_all_fixed_iff_dvd`).

[`Gnosis/AeonTwelveCarrierList.lean`](Gnosis/AeonTwelveCarrierList.lean) strings the **next** bookkeeping layer toward carrier-heavy
storytelling: **gcd** divisibility for the stride exponent, one **native_decide** link from **`rotateIndex`**
to **`cyclicSucc`**, a **GodTwelveSlice** conservation hook at **`R = 12`**, and **rotPairNat**
invariance of **`shortChord`** across the **66** pairs.

### Honest-unification exemplar: prove the dichotomy, refute the over-claim

[`Gnosis/ErgodicCutoffDuality.lean`](Gnosis/ErgodicCutoffDuality.lean) is the exemplar for
the Sardis-warning's positive use: it takes a sweeping "everything is the same torus
automorphism quotient" pitch and resolves it into what `lake build` will actually carry.
The disciplined moves:

- **Separate the regimes instead of identifying them.** `Returns f T x := iter f T x = x`
  (conservative) versus `DissipativeSystem` with a monovariant that drops by 1 per step
  (`step_sub_one`, `dissipative_mono_after`, `dissipative_absorbs`). The genuine theorem is
  a **dichotomy**: `dissipative_not_periodic` proves a dissipative state with positive
  monovariant is **aperiodic**, so the two regimes meet only at the absorbing point. This
  replaces the prose "healing IS scrambling" with the proved "healing is the dissipative
  *complement* of a closed orbit."
- **Demote coincidences to coincidences.** The cat map on `(Z/5)²` and the out-shuffle on
  12 cards share **period 10** (reused from `AeonNoise`), but `distinct_orbit_structure`
  `decide`s that their fixed-point counts differ (1 vs 2): same period, **not** the same
  quotient. Equal magnitudes are not a shared invariant. The sibling
  [`Gnosis/ErgodicCutoffCycleType.lean`](Gnosis/ErgodicCutoffCycleType.lean) carries this
  to a full **antitheorem**: it proves both maps have order *exactly* 10 (period set =
  multiples of 10, via `period_dvd`) yet have different cycle types
  (`1+2+2+10+10` vs `1+1+10`), with `actions_are_not_conjugate` certifying the
  fingerprint mismatch under *zero* axioms. An antitheorem — a proved non-match where a
  match was expected — is as load-bearing here as a theorem.
- **Subsume, don't restate.** `cancerDissipative` instantiates the generic absorbing law,
  and `iter_eq_iterateRestoration` bridges back to `CancerTopology.iterateRestoration`, so
  `cancer_recovers_in_seven_bridged` falls out as a *corollary* of the abstract theorem —
  the "7" is exposed as `gbmCombined.deficit = 9 - 2`, an instance parameter, never a constant.
- **Name the open obligation in prose.** The "7 riffle shuffles" in
  `Gnosis/Mesh/MeshCriticalThresholds.lean` is a hard-coded entry in `getThreshold`, not a
  proved Markov / total-variation cutoff (the `threshold_*` theorems only show a threshold
  is *reachable*). Until a real mixing-time witness exists, riffle-7 stays a **label**, so it
  is deliberately **excluded** from the duality rather than smuggled in. (The auto-generated
  [`MCP_OPEN_OBLIGATIONS.md`](MCP_OPEN_OBLIGATIONS.md) only counts `sorry`/`admit`/`axiom`
  tokens; an unproved *label* like this is invisible to it and must be tracked in prose here.)

Axioms: `propext` only (the `by_cases` stays constructive through `Nat`'s `DecidableEq`); no
`Classical.choice`, no `sorryAx`. The lesson: a top-down "they are all one thing" story earns
its keep only at the granularity where `lake build` still bears weight — prove the relation
that survives, and label the rest.

### Quality-margin admissibility: the bound and its antitheorem

The distributed-inference quality gate — an admitted model must *predict the expected token*,
not merely carry the catalog name — is the operational twin of the Sardis warning, and it has a
clean bound+antitheorem certificate. Model a logit vector as `Int`-scaled scores over a finite
token index (argmax is scale-invariant, so integers are faithful and keep the proof `omega`-free).
Two halves, both load-bearing:

- **The bound (live witness).** If `i⋆` is the strict argmax of `L` with runner-up margin `γ`,
  and a substituted vector `L'` (a cross-model cache hit, or an approximate / replayed
  reconstruction) satisfies the sup-norm bound `∀ k, |L k − L' k| < τ` with `2·τ ≤ γ`, then `i⋆`
  is *also* the strict argmax of `L'`: the substitution is indistinguishable from the real
  computation **to the gate**. It closes pairwise (`∀ j ≠ i⋆, L' j < L' i⋆`) with the Int
  cookbook (`Int.add_lt_add_right`, `Int.lt_of_lt_of_le`, `Int.lt_trichotomy` — see "Bridging Nat
  with Int") — never `omega`.

- **The antitheorem (Sardis signature).** The bound is *tight*: a witness with `2·τ > γ` flips the
  argmax while the cache still **reports a hit**. That is precisely "a name that liveth, and is
  dead" — a green status over a wrong answer. The proved flip-witness is as load-bearing as the
  bound (same discipline as `ErgodicCutoffDuality`'s `distinct_orbit_structure`): it forbids
  accepting any approximate / cross-model hit whose tolerance is not provably below `γ/2`.

Doctrine: a content-addressed, cross-model, or replay inference cache earns admission only at the
granularity where the margin bound still carries it; beyond `γ/2` it must **miss, not lie**. (This
is the formal floor under the runtime corruptors found by the quality gate this cycle — an
unbounded Q-filter / replay substitution silently violated `2τ ≤ γ` and flipped the token.)

The certificate is live Init-only in
[`Gnosis/QualityMarginCacheAdmissibility.lean`](Gnosis/QualityMarginCacheAdmissibility.lean):
`argmax_preserved` (the bound), `predicted_token_preserved` (gate equivalence),
`cache_hit_admissible`, and the tightness antitheorem `argmax_can_flip_when_bound_violated`
(a closed `Fin 2` flip witness). The bound chains three named Int helpers
(`lt_add_of_neg_lt_sub`, `sub_lt_of_sub_lt`, `add_tau_le_sub_tau` — the margin absorbing two
tolerances) through `Int.lt_trans`/`Int.lt_of_lt_of_le`; `#print axioms` is `propext` only — no
`omega`, no Mathlib, no `Quot.sound`. The lineage matters: an earlier `omega` draft *built* but
was Sardis-mode (a name, not the live Init witness) until this port re-derived it from the
cookbook.

### The shared core (and where it stops)

When the conjecture arose that this ties together "most of the contrarian formalizations,"
the honest move was to test it, not toast it. [`Gnosis/FiniteDynamicsCore.lean`](Gnosis/FiniteDynamicsCore.lean)
extracts the genuinely shared spine — `iter`, `Returns`/`ReturnsAll`, the order theorem
`period_dvd`, the conservative `returns_conserves`, the dissipative `dissipative_not_periodic`,
and two **antitheorem schemas** (`separates`: a differing invariant refutes an identity;
`not_forced_by_witness`: a witness refutes "structure forces property", both *axiom-free*).
`ErgodicCutoffDuality` and `ErgodicCutoffCycleType` now import it rather than carrying their
own copies — single source of truth.

[`Gnosis/FiniteDynamicsUnification.lean`](Gnosis/FiniteDynamicsUnification.lean) is the
demonstration: through that one core it re-derives the discrete-clock period (substrate of
`DiscreteClosedTimelikeStep` / the `AeonTwelve*` clocks), the cat-map order at modulus 3 and 5
(`ArnoldCatMapOrder5`), and the Collatz `{1,2,4}` cycle (`CollatzOneTwoFourBraid`), and emits
fresh antitheorems (`out_shuffle_ne_clock`, `catMod3_ne_catMod5`) from `separates`.

But the tie is bounded, and the module says so. The `Gnosis/Contrarian/` corpus is dominated
by *inversions* (`chaos_is_order`, `efficiency_is_fragility`, `death_limit_enables_vitality`):
thin bounded consequences of a structure field, sharing the anti-theory **stance**, not this
**core**. The claim "one structure unifies all 90 contrarian files" would itself be the
recursive-trap overreach this manifesto warns against. So the file states a *falsifiable*
conjecture instead — every Contrarian headline factors as a `separates`, a
`not_forced_by_witness`, a monovariant inversion, or a `period_dvd`/conservation/dissipation
fact — with the falsifying test named: find one that fits none.

## How you close goals instead of `omega`

After `unfold`, the goal almost always fits one of the patterns in the cookbook
below. Reach for named Init lemmas in order:

- Successor-shaped: `0 < n + 1`, `n < n + 1`, `n ≤ n + 1`.
- Saturating sub identities: `(n - 1) + 1 = n` (with `0 < n`), `(n + 1) - 1 = n`.
- Add commutativity / associativity / right-comm.
- Monotonicity through one operator (sub-left, add-right, mul-right).
- Closed numeric goals (no free vars after unfolds): `decide`.
- Impossible match branches: `absurd h (by decide)`.

Harder stacks (3+ interacting `Nat` sub facts, `Int`/`Nat` casts, long modular
rewrites) **still** must finish without `omega`: peel one inequality at a time,
name intermediate facts, and factor helpers until each step is a single
cookbook pattern. If a proof is stuck, the fix is a lemma split or a sharper
statement — not a tactic exception.

`decide` is acceptable for *closed* numeric goals (no free vars) — it's still
kernel-checked, just slower than a named lemma. `native_decide` is acceptable
for large finite checks (it trusts the compiler too, but the trade is huge
search spaces).

For branch-heavy Init-only proofs, prefer `by_cases h : P` followed by
`simp [definition, h]` over `split_ifs` when the file has to stay in the Init
surface. This has been the cleanest way to keep each branch small enough for
named Init lemmas instead of disallowed arithmetic tactics.

## Cookbook

### Successor / `+1` (clinamen) shapes

```lean
example (n : Nat) : 0 < n + 1 := Nat.succ_pos n
example (n : Nat) : n < n + 1 := Nat.lt_succ_self n
example (n : Nat) : n ≤ n + 1 := Nat.le_succ n
example {n m : Nat} (h : n ≤ m) : n + 1 ≤ m + 1 := Nat.succ_le_succ h
example (n : Nat) : 0 ≤ n := Nat.zero_le n
```

`0 < n` and `1 ≤ n` are *definitionally equal* in Lean 4 — pass `hK : 1 ≤ K`
where `0 < K` is expected, no conversion needed.

### Saturating subtraction `a - b`

This is where proofs often used to reach for `omega`; Init has clean lemmas:

```lean
-- (n - 1) + 1 = n, given 0 < n
example {n : Nat} (h : 0 < n) : (n - 1) + 1 = n := Nat.sub_add_cancel h

-- (n + 1) - 1 = n  (no hypothesis needed; pure structural)
example (n : Nat) : (n + 1) - 1 = n := Nat.add_sub_cancel

-- (a + b) - a = b
example (a b : Nat) : a + b - a = b := Nat.add_sub_cancel_left a b
-- ⚠ In Lean 4.28 this lemma takes BOTH args explicitly. If you write
--   `exact Nat.add_sub_cancel_left` Lean asks for the args.

-- a - b ≤ a
example (a b : Nat) : a - b ≤ a := Nat.sub_le a b

-- monotone: more rejected ⇒ less weight (antitone in subtrahend)
example {n m : Nat} (h : n ≤ m) (k : Nat) : k - m ≤ k - n :=
  Nat.sub_le_sub_left h k

-- "k ≤ a, a < k + n ⇒ a - k < n"
example {k a n : Nat} (h₁ : k ≤ a) (h₂ : a < k + n) : a - k < n :=
  Nat.sub_lt_left_of_lt_add h₁ h₂

-- inverse phrasings
example {k m n : Nat} (h : k + m ≤ n) : m ≤ n - k :=
  Nat.le_sub_of_add_le h
example {k m n : Nat} (h : k + m < n) : m < n - k :=
  Nat.lt_sub_of_add_lt h

-- m + (n - m) = n  (commuted Nat.sub_add_cancel)
example {m n : Nat} (h : m ≤ n) : m + (n - m) = n := Nat.add_sub_of_le h

-- saturation collapses at boundaries
example {a b : Nat} (h : a ≤ b) : a - b = 0 := Nat.sub_eq_zero_of_le h
example {a b : Nat} (h : a - b = 0) : a ≤ b := Nat.le_of_sub_eq_zero h
example {a b : Nat} (h : a < b) : 0 < b - a := Nat.sub_pos_of_lt h
example (n : Nat) : n - n = 0 := Nat.sub_self n
example (n : Nat) : n - 0 = n := Nat.sub_zero n
```

### Addition manipulation

```lean
example (a b c : Nat) : a + b + c = a + c + b := Nat.add_right_comm a b c
example (a b : Nat) : a + b = b + a := Nat.add_comm a b
example (a b c : Nat) : a + b + c = a + (b + c) := Nat.add_assoc a b c

example (a b : Nat) : a ≤ a + b := Nat.le_add_right a b
example (a b : Nat) : a ≤ b + a := Nat.le_add_left a b
example {a b : Nat} (h : 0 < b) : a < a + b := Nat.lt_add_of_pos_right h
example {a b : Nat} (h : 0 < a) : b < a + b := Nat.lt_add_of_pos_left h

example {a b : Nat} (h : a ≤ b) (k : Nat) : a + k ≤ b + k :=
  Nat.add_le_add_right h k
example {a b : Nat} (h : a < b) (k : Nat) : a + k < b + k :=
  Nat.add_lt_add_right h k
```

`Nat.add` reduces by recursion on the **right** argument, so:

```lean
example (a b : Nat) : a + (b + 1) = a + b + 1 := rfl   -- definitional!
```

Use this constantly: `n + (k + 1)` is `(n + k) + 1` for free.

### Multiplication

```lean
example (m k : Nat) (h : 0 < k) : m ≤ k * m := Nat.le_mul_of_pos_left m h
example (a b : Nat) (v : Nat) (h : a ≤ b) : a * v ≤ b * v :=
  Nat.mul_le_mul_right v h

example (n : Nat) : 2 * n = n + n := Nat.two_mul n
example (n m : Nat) : n * (m + 1) = n * m + n := Nat.mul_succ n m
example (n m : Nat) : (n + 1) * m = n * m + m := Nat.succ_mul n m
```

### Division

```lean
example (n k : Nat) : n / k ≤ n := Nat.div_le_self n k
-- 0 < k ≤ n ⇒ 0 < n / k
example {k n : Nat} (h₁ : k ≤ n) (h₂ : 0 < k) : 0 < n / k :=
  Nat.div_pos h₁ h₂
-- antitone in divisor: dividing by more gives less
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : 0 < a) : c / b ≤ c / a :=
  Nat.div_le_div_left h₁ h₂
```

### Order, transitivity, antisymmetry

```lean
example (n : Nat) : n ≤ n := Nat.le_refl n
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := Nat.le_trans h₁ h₂
example {a b c : Nat} (h₁ : a < b) (h₂ : b ≤ c) : a < c := Nat.lt_of_lt_of_le h₁ h₂
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := Nat.lt_of_le_of_lt h₁ h₂
example {a b : Nat} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := Nat.le_antisymm h₁ h₂
example {a b : Nat} (h₁ : a < b) : a ≤ b := Nat.le_of_lt h₁
example {a b : Nat} (h : ¬ b < a) : a ≤ b := Nat.le_of_not_gt h
example {a b : Nat} (h : a ≤ b) : ¬ b < a := Nat.not_lt_of_le h
example (n : Nat) : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
example {n : Nat} (h : n ≠ 0) : 0 < n := Nat.pos_of_ne_zero h
example (n : Nat) : ¬ n < n := Nat.lt_irrefl n
example (a b : Nat) : a < b ∨ b ≤ a := Nat.lt_or_ge a b
example (a b : Nat) : a ≤ b ∨ b < a := Nat.le_or_lt a b
example {a b : Nat} (h : a ≠ b) : a < b ∨ b < a := Nat.lt_or_gt_of_ne h
example (a b : Nat) : a ≤ b ∨ b ≤ a := Nat.le_total a b
```

### Modular arithmetic (`%`)

Init has clean lemmas for the common shapes; only break out manual reasoning
when none fit:

```lean
example (n k : Nat) : (n + k) % k = n % k := Nat.add_mod_right n k
example {n k : Nat} (h : n < k) : n % k = n := Nat.mod_eq_of_lt h
example (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := Nat.add_mod a b n
-- multiples are zero mod themselves
example (k m : Nat) (h : 0 < k) : 0 < k * m + k - k * m := by
  exact Nat.sub_pos_of_lt (Nat.lt_add_of_pos_right h)
```

The pattern `(n + 6) % 12 + 6` collapses via `← Nat.add_mod` then
`Nat.add_mod_right` (`ToneCircle.double_ring_involution`).

### Bridging Nat with Int (the casting toolkit)

These come up every time a definition mixes `Nat` and `Int` (e.g.
`topologicalDeficit`, `pathCostDelta`, `centralCharge`). Same shape every
time: Int comparison ↔ Nat comparison through one cast.

```lean
-- order
example (n m : Nat) (h : n ≤ m) : ((n : Int)) ≤ ((m : Int)) := Int.ofNat_le.mpr h
example (n m : Nat) : ((n : Int)) ≤ ((m : Int)) → n ≤ m := Int.ofNat_le.mp
example (n m : Nat) (h : n < m) : ((n : Int)) < ((m : Int)) := Int.ofNat_lt.mpr h
example (n m : Nat) : ((n : Int)) < ((m : Int)) → n < m := Int.ofNat_lt.mp
example (n m : Nat) (h : n = m) : ((n : Int)) = ((m : Int)) := Int.ofNat_inj.mpr h
example (n m : Nat) : ((n : Int)) = ((m : Int)) → n = m := Int.ofNat_inj.mp
-- positivity / sign of Int differences
example (n : Nat) (h : 0 < n) : 0 < ((n : Int)) := Int.natCast_pos.mpr h
example {a b : Int} (h : a ≤ b) : 0 ≤ b - a := Int.sub_nonneg_of_le h
example {a b : Int} (h : 0 ≤ b - a) : a ≤ b := Int.le_of_sub_nonneg h
example {a b : Int} (h : a ≤ b) : a - b ≤ 0 := Int.sub_nonpos_of_le h
example {a b : Int} (h : a - b ≤ 0) : a ≤ b := Int.le_of_sub_nonpos h
example {a b : Int} (h : a < b) : 0 < b - a := Int.sub_pos_of_lt h
example {a b : Int} (h : 0 < b - a) : a < b := Int.lt_of_sub_pos h
example {a b : Int} (h : a < b) : a - b < 0 := Int.sub_neg_of_lt h
example {a b : Int} (h : a - b < 0) : a < b := Int.lt_of_sub_neg h
example {a b : Int} (h : a - b = 0) : a = b := Int.eq_of_sub_eq_zero h
-- algebra used to chain through Int diff goals
example (a b : Int) : a - b - (a - b) = 0 := Int.sub_self _
example (n k m : Int) : (n + k) - (m + k) = n - m := Int.add_sub_add_right n k m
example (a b : Int) : -(a - b) = b - a := Int.neg_sub a b
example (a b c : Int) : a + b - c = a + (b - c) := Int.add_sub_assoc a b c
example (n : Int) : 2 * n = n + n := Int.two_mul n
example (a b c : Int) : a * (b - c) = a * b - a * c := Int.mul_sub a b c
example {a b c : Int} (h : a ≤ b) (k : Int) : a + k ≤ b + k := Int.add_le_add_right h k
example {a b c : Int} (h : a ≤ b) : c - b ≤ c - a := Int.sub_le_sub_left h c
example {a b c : Int} (h : a ≤ b) : a - c ≤ b - c := Int.sub_le_sub_right h c
example {a b k : Int} (h₁ : 0 ≤ k) (h₂ : a ≤ b) : k * a ≤ k * b :=
  Int.mul_le_mul_of_nonneg_left h₂ h₁
example (n : Int) : n - 1 < n := Int.sub_lt_self n (by decide)
example (n m : Nat) : ((n * m : Nat) : Int) = (n : Int) * (m : Int) := Int.natCast_mul n m
-- three-way Int compare for ∨ ∨ goals
example (a b : Int) : a < b ∨ a = b ∨ b < a := Int.lt_trichotomy a b
```

The recipe for an Int-cast iff (e.g. `2 * (rows : Int) - sat ≥ 0 ↔ sat ≤ 2 * rows`):

1. Apply `Int.sub_nonneg` (or `Int.sub_eq_zero`, `Int.sub_pos_of_lt`, etc.)
   to peel the `0 R …` shell.
2. `rw [Int.natCast_mul]` to fuse `2 * (n : Int)` into `((2*n : Nat) : Int)`.
3. `Int.ofNat_le.mp` / `.mpr` to land on the Nat side.

`ManifoldReadiness.carrier_ready_iff_half_saturation` is the canonical example.

### Multiplication / division (more)

```lean
example (a b k : Nat) (h : 0 < k) : k * a < k * b ↔ a < b := Nat.mul_lt_mul_left h
example {a b c : Nat} (h : 0 < c) (heq : c * a = c * b) : a = b :=
  Nat.eq_of_mul_eq_mul_left h heq
example {a b : Nat} (h : 0 < a) (h' : 0 < b) : 0 < a * b := Nat.mul_pos h h'
example {a b : Nat} (h : a ≤ b) (k : Nat) : a / k ≤ b / k := Nat.div_le_div_right h
example {n k : Nat} (h₁ : k ≤ n) (h₂ : 0 < k) : 0 < n / k := Nat.div_pos h₁ h₂
example (n m : Nat) : n * (m + 1) = n * m + n := Nat.mul_succ n m
example (n m : Nat) : (n + 1) * m = n * m + m := Nat.succ_mul n m
example (a b c : Nat) : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example (a b c : Nat) : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example (a b c : Nat) : a * (b - c) = a * b - a * c := Nat.mul_sub a b c
```

### Equality lifting through operators

When the goal is `f a = f b` and you have `a = b`, prefer `congrArg`:

```lean
example {α β : Type} (f : α → β) {x y : α} (h : x = y) : f x = f y :=
  congrArg f h

-- worked example: lift `h : c = d` through `· + rate`
example (c d rate : Nat) (h : c = d) : c + rate = d + rate := congrArg (· + rate) h
```

This pattern often replaces a `simp [h]` plus arithmetic-tactic chain with a
single term.

### Discharging impossible cases

When `match` / `cases` produces a branch whose hypothesis is contradictory:

```lean
-- hn : 1 ≤ 0 — impossible
example (hn : 1 ≤ 0) : False := absurd hn (by decide)

-- hn : 2 ≤ n + 1, but match branch already pinned n + 1 = 1
example (hn : 2 ≤ 1) : False := absurd hn (by decide)

-- n + 22 ≤ 21 for any Nat n — impossible because 21 < 22 ≤ n + 22
example (n : Nat) (h21 : n + 22 ≤ 21) : False :=
  Nat.not_le_of_lt
    (Nat.lt_of_lt_of_le (by decide : (21 : Nat) < 22) (Nat.le_add_left 22 n))
    h21

-- universal: n < 0 is impossible for Nat
example (n : Nat) (h : n < 0) : False := Nat.not_lt_zero n h
```

### Anchor cleanup

When you encounter a theorem written as `: True := ...`, do not preserve the
anchor. Rephrase it into a concrete reflexive equality, a direct existence
witness, or a finite invariant:

```lean
example (x : α) : x = x := rfl
example : ∃ x : Nat, x = 0 := ⟨0, rfl⟩
example (f : Nat → Nat) : ∀ n, f n = f n := by intro; rfl
```

This is the cleanest replacement for vacuous chapel anchors.

### Nat → Int casts

`((n + 1 : Nat) : Int) = (n : Int) + 1` reduces by `rfl`. Past that, lean on:

```lean
example (a : Int) (b : Nat) : a - ((b + 1 : Nat) : Int) = a - (b : Int) - 1 := by
  show a - ((b : Int) + 1) = a - (b : Int) - 1
  rw [show (a - (b : Int) - 1) = a + (-(b : Int) + (-1)) from by
        rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_assoc, ← Int.neg_add]]
  rw [Int.sub_eq_add_neg, Int.neg_add]
```

Genuine Int-linear chains are high-effort but **still** `omega`-free — see
the `meta_truth_constancy` proof in `Gnosis/TopologicalMetabolism.lean` for a
working Init/`Int` rewrite pattern.

### Bool / Prop coercion (the Prop→Bool refactor)

If you switch a definition's return type from `Prop` to `Bool` and the body
mixes `Bool && Prop`, Lean coerces the Prop side via `decide`. To unpack
`f x = true` where `f` returns Bool:

```lean
-- decide_eq_true_iff and decide_eq_false_iff take NO explicit args in 4.28
example (p : Prop) [Decidable p] (h : decide p = true) : p :=
  decide_eq_true_iff.mp h
-- Functional shortcuts (preferred for term-mode):
example (p : Prop) [Decidable p] (h : decide p = true) : p := of_decide_eq_true h
example (p : Prop) [Decidable p] (h : ¬ p) : decide p = false := decide_eq_false h
example (p : Prop) [Decidable p] (h : decide p = false) : ¬ p := of_decide_eq_false h

-- Bool && Bool unpack:
example (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true :=
  (Bool.and_eq_true a b).mp h
```

Pattern for nested `Bool` defs (e.g. `truthState p m d := truthExists p m ∧ isCoherent d`,
both Bool, so the body's `∧` is on Props with the Bools coerced via `= true`,
then the whole thing is `decide`'d to Bool):

```lean
intro hTruth                                              -- hTruth : truthState p m d = true
have hPair : truthExists p m = true ∧ isCoherent d = true :=
  of_decide_eq_true hTruth                                -- peel one decide layer
exact use_of_pair hPair.1 hPair.2
```

If a `def f : Bool := P` won't elaborate because `P : Prop` needs an
explicit `decide`, write `def f : Bool := decide P`. Lean does not auto-coerce
Prop → Bool inside `def` bodies even though it does so inside expressions.

### Recurring patterns from semantic-space

These are the shapes that show up over and over once you've worked through a
few dozen Init-only modules — recognize them in the goal and reach straight for
the named lemma.

#### Reflexive goals: hypothesis *is* the goal

A black-box arithmetic tactic often closes a goal that — after `unfold` and
Lean's defeq — is literally one of the hypotheses, because of definitional
equalities like `0 < n ≡ 1 ≤ n` or `Nat.succ_le ≡ Nat.lt`. Try `exact h`
*first* (Rustic Church: never use `omega` here either).

```lean
-- 0 < x ⊢ 1 ≤ x  →  exact h  (defeq)
-- a > b ⊢ a ≥ b + 1  →  exact h  (Nat.lt unfolds to Nat.succ_le)
-- score > 0 ⊢ score ≥ 1  →  exact h
```

If that fails, try `Nat.le_of_lt h`, `Nat.lt_of_le_of_ne h hne`,
`Nat.succ_le_of_lt h`, `Nat.le_of_succ_le_succ h`.

#### `congrArg`: lift equality through a function

```lean
example (c d rate : Nat) (h : c = d) : c + rate = d + rate := congrArg (· + rate) h
```

Almost any `simp [h]`-then-arithmetic chain on a free-variable goal where the
`simp` step is just substituting an equality reduces to one `congrArg`.

#### Substitution-then-`Nat.lt_irrefl` for impossible `<`

When a hypothesis combined with a substitution produces `n < n`, refute
directly:

```lean
exact Nat.lt_irrefl 0 (h_score ▸ h_pos)   -- h_score : x = 0, h_pos : x > 0
```

#### Concrete-Nat-cast `decide` after `▸`

Closed-numeric goals with a free var after substitution: `▸` to substitute,
then `decide` for the residual literal.

```lean
exact h ▸ (by decide : (10 : Nat) ≥ 5)   -- h : x = 10, goal : x ≥ 5
```

#### Three-summand Nat sum = 0 ⇒ each summand = 0

When you need `w = 0`, `o = 0`, `d = 0` from `w + o + d = 0`, peel via two
applications of `Nat.add_eq_zero_iff.mp`:

```lean
have ⟨hwo, hd⟩ := Nat.add_eq_zero_iff.mp h_sum  -- (w + o) + d = 0
have ⟨hw, ho⟩ := Nat.add_eq_zero_iff.mp hwo    -- w + o = 0
```

Same trick generalizes to any `(((a + b) + c) + d) + ... = 0` chain.

#### Three-summand Nat sum > 0 from one summand > 0

The mirror image: when `0 < w + o + d` from `0 < w` (or `0 < o`, `0 < d`):

```lean
exact Nat.lt_of_lt_of_le h_w (Nat.le_add_right w (o + d))   -- if 0 < w
exact Nat.lt_of_lt_of_le h_d (Nat.le_add_left d (w + o))    -- if 0 < d
-- Middle summand: combine with Nat.add_assoc
```

Or universal: case-split with `cases w`, `cases o`, `cases d` and refute the
all-zero case from the contrapositive. Used in
`AttentionScalingLaw.non_vacuum_experiences_pull` and
`TemporaryNoise.everything_else_is_temporary`.

#### `simp only [if_pos h]` / `simp only [if_neg h]` to surface a branch

When goal is `(if cond then A else B) ≤ ...` and you have `h : cond` (or
`¬cond`):

```lean
simp only [if_pos h]   -- replaces the if-expr with A
-- now prove A ≤ ...
```

This avoids `simp [definitionWithIf, h]` which can over-aggressively
collapse the surrounding goal shape (e.g. destroying a needed `∧`).
Used in `FailureController.chosen_failure_action_coefficient_minimal`.

#### `match Int.lt_trichotomy …` for ∨ ∨ goals over Int

```lean
match Int.lt_trichotomy a b with
| Or.inl hLt => exact Or.inr (Or.inr hLt)
| Or.inr (Or.inl hEq) => exact Or.inr (Or.inl hEq)
| Or.inr (Or.inr hGt) => exact Or.inl hGt
```

Used in `ComputationalStateTransitionsAsPathDivergence.paths_from_same_state_comparable`.

#### `cases p.field` over enum + `decide` per branch for closed bound

For goals like `flagsByte p < 16` where `p` has 4 Bool-flag fields,
`cases` per field and let `decide` close each:

```lean
cases p.flag1 <;> cases p.flag2 <;> cases p.flag3 <;> cases p.flag4 <;>
  cases p.optionField <;> simp <;> decide
```

#### Closed-form Nat sub identity peel: `Nat.sub_sub_self`

When the goal is `x - (x - y) = y` (with `y ≤ x`), the recipe is exactly
`Nat.sub_sub_self h`. This shows up after every saturating-subtraction
unfold. Don't manually decompose — use the lemma.

#### `n + (k + 1) = (n + k) + 1` for free

`Nat.add` is defined by recursion on the right argument, so the right-shift
of `+1` reduces by `rfl`. Use this to make goals match named lemma shapes
without an explicit `Nat.add_succ` rewrite.

#### Hypothesis projection from simp-decomposed `∧`

When `simp [definitionThatIsAnAnd] at h` produces `h : (A ∧ B) ∧ C`,
the components are `h.left.left`, `h.left.right`, `h.right`. Use these
directly in term-mode rather than re-introducing fresh names.

```lean
exact ⟨h.left.left, h.left.right, h.right⟩   -- reshape (A ∧ B) ∧ C as A ∧ B ∧ C
```

Used pervasively in `*Predictions*` and `Anti*` modules.

#### Polynomial expansion via `Nat.mul_add` + `Nat.add_mul` + `ac_rfl`

For shapes like `(n + 1) * (b + 1) = n*b + n + b + 1`:

```lean
rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
simp [Nat.mul_one, Nat.one_mul]
ac_rfl
```

The `simp [Nat.mul_one, Nat.one_mul]` removes the `* 1` artifacts; `ac_rfl`
normalizes the AC tree.

#### `← Nat.add_mod` to fold modular sums

The pattern `((n + k) % m + k) % m` collapses via reverse `Nat.add_mod`
combined with `Nat.add_mod_right`:

```lean
rw [show (n + 6) % 12 + 6 = ((n + 6) + 6) % 12 from ...]
-- then Nat.add_assoc + Nat.add_mod_right
```

Used in `ToneCircle.double_ring_involution`.

#### `Nat.add_sub_cancel_left` requires explicit args in Lean 4.28

```lean
example (a b : Nat) : a + b - a = b := Nat.add_sub_cancel_left a b
```

Bare `Nat.add_sub_cancel_left` won't elaborate — both args must be
supplied. Same for `Nat.add_sub_cancel` (no explicit args, it's the
saturating one).

#### Deriving `≠` from `=` + positivity

```lean
-- From x = 0 and y > 0, prove x ≠ y:
rw [h_eq]                  -- rewrites x to 0
exact Nat.ne_of_lt h_pos   -- 0 < y ⇒ 0 ≠ y
```

Direction matters — `Nat.ne_of_lt : a < b → a ≠ b`. After `rw [eq_to_zero]`,
no `.symm` is needed.

### `repeat constructor` does not descend

In Lean 4.28, `repeat tac` only repeats on the current main goal until `tac`
fails, then stops. For an N-ary `∧` chain `A ∧ B ∧ C ∧ ... ∧ Z`, the first
`constructor` produces goals `A` and `B ∧ C ∧ ... ∧ Z`; `constructor` fails
on `A` so `repeat` stops with two goals open, not N.

For master-bundle theorems, prefer:

```lean
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· exact ...
· exact ...
...
```

with one placeholder per top-level conjunct.

## Worked replacement patterns

These are the substitutions that came up repeatedly while the workspace was
moved to Init-only proofs. If you see the LHS shape in a goal, the RHS is the
usual Rustic Church closure.

| Goal shape | Replacement |
|---|---|
| `0 < n + 1` | `Nat.succ_pos _` |
| `n < n + 1` | `Nat.lt_succ_self _` |
| `n ≤ n + 1` | `Nat.le_succ _` |
| `n ≤ n + k` | `Nat.le_add_right _ _` |
| `n < n + k` (with `0 < k`) | `Nat.lt_add_of_pos_right h` |
| `(n - 1) + 1 = n` (with `0 < n`) | `Nat.sub_add_cancel h` |
| `(n + 1) - 1 = n` | `Nat.add_sub_cancel` |
| `a + b - a = b` | `Nat.add_sub_cancel_left a b` |
| `m + (n - m) = n` (with `m ≤ n`) | `Nat.add_sub_of_le h` |
| `n - m ≤ n` | `Nat.sub_le n m` |
| `k - m ≤ k - n` (with `n ≤ m`) | `Nat.sub_le_sub_left h k` |
| `0 < n - m` (with `m < n`) | `Nat.sub_pos_of_lt h` |
| `1 ≤ K - 1` (with `2 ≤ K`) | `Nat.le_sub_of_add_le h` |
| `1 < K - 1` (with `3 ≤ K`) | `Nat.lt_sub_of_add_lt (Nat.lt_of_lt_of_le (by decide) h)` |
| `a + b + c = a + c + b` | `Nat.add_right_comm a b c` |
| `a + 0 = a` | `Nat.add_zero a` |
| `a = b` from `a ≤ b` and `b ≤ a` | `Nat.le_antisymm h₁ h₂` |
| `a < c` from `a < b` and `b ≤ c` | `Nat.lt_of_lt_of_le h₁ h₂` |
| `n ≤ k * n` (with `0 < k`) | `Nat.le_mul_of_pos_left n h` |
| `a * v ≤ b * v` (with `a ≤ b`) | `Nat.mul_le_mul_right v h` |
| `n * (m + 1) = n * m + n` | `Nat.mul_succ n m` |
| `2 * n = n + n` | `Nat.two_mul n` |
| `False` from impossible Nat literal | `absurd h (by decide)` |
| Closed numeric (no free vars) | `decide` |
| Closed numeric, big search space | `native_decide` |

## Completed audit guard for banned tactics

The Init-only rebuild is complete. This section is a regression guard for files
revived from history or newly introduced with banned tactics; it is not an
open migration track.

1. Inventory: `grep -nE "\bomega\b" Gnosis/Foo.lean` (Rustic Church: **must be
   zero** before merge).
2. Bulk attempt **only on closed goals**: replace `by omega` / trailing
   `omega` with `by decide` / `decide` where the goal has no free variables
   after `unfold`.
3. Build: `lake build Gnosis.Foo 2>&1 | grep "^error" | sed -E 's|.*lean:([0-9]+):.*|\1|' | sort -un`.
4. Each line that errored has a free variable — **do not** restore `omega`.
   Convert by hand using the cookbook above (named `Nat`/`Int` lemmas, case
   splits, helper lemmas).
5. The lines that didn't error are now `decide`-closed. Move on.
6. Re-build until green, run full `lake build` to make sure no downstream consumer broke.

Most files split roughly 70/30: closed numerics (bulk → `decide`) vs.
free-variable goals (hand-translate using the cookbook). The hand-translate
work usually compresses several opaque steps into one Init lemma name once
you spot the shape.

## Cracking 3+ saturating-sub proofs

*During the completed Init rebuild, these shapes were the slowest to unwind. After
[`Gnosis/HumanCompiler.lean`](Gnosis/HumanCompiler.lean),
[`Gnosis/SelfHostingOptimality.lean`](Gnosis/SelfHostingOptimality.lean),
and [`Gnosis/TenModeUnification.lean`](Gnosis/TenModeUnification.lean)
landed Init-only, the cookbook recipe for them became standard — not a
temporary exception.*

The trick is naming each fact and chaining them explicitly — a black-box
arithmetic tactic would fuse the same facts in one opaque step; Rustic Church
requires the named chain.

### Pattern 1: Convergence by induction on cost ladder (`stable_from`)

The shape: `∀ v, cost s ≤ v → ∃ N, ...`. Induct on `v`. Two key sub-cases:

- **Strict drop, recurse one budget tighter.** From `cost (s+1) < cost s`
  and `cost s ≤ v + 1`, derive `cost (s+1) ≤ v` by
  `Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdrop hle)`.
  Then bump the existential's `N` upper bound from `s+1 ≤ N` to `s ≤ N` via
  `Nat.le_trans (Nat.le_succ s) hN1`.
- **Plateau (no drop, no slack).** From `¬(cost (s+1) < cost s)` get
  `cost s ≤ cost (s+1)` via `Nat.le_of_not_lt`, then `cost (s+1) = cost s`
  via `Nat.le_antisymm (h s) hSleStep`. From `¬(cost (s+1) ≤ v)` get
  `v + 1 ≤ cost (s+1)` via `Nat.succ_le_of_lt (Nat.lt_of_not_le hle2)`.
  Bridge through the equality and you have `cost s = v + 1`.

The pattern that closes the inner "every later step also equals v+1" lemma:
`Nat.le_antisymm (hval ▸ monotone_descent ...) (Nat.le_of_not_lt hlt)`.

### Pattern 2: `n - r_j < n - r_i` via difference peeling

Given `r_i < r_j ≤ n`, prove `n - r_j < n - r_i`. Don't reach for sub
inequalities directly — peel `n - r_j = (n - r_i) - (r_j - r_i)` and apply
`Nat.sub_lt_self`:

```lean
have hLe : r_i ≤ r_j := Nat.le_of_lt h
have hDiffPos : 0 < r_j - r_i := Nat.sub_pos_of_lt h
have hDiffLeT : r_j - r_i ≤ n - r_i := Nat.sub_le_sub_right bj r_i
have hPeel : n - r_j = (n - r_i) - (r_j - r_i) := by
  rw [Nat.sub_sub, Nat.add_sub_of_le hLe]
rw [hPeel]
exact Nat.sub_lt_self hDiffPos hDiffLeT
```

### Pattern 3: Master-bundle by `Nat.lt_or_ge` + bound-style refute

When the goal is `f x = K ↔ x = K_value`, split on `x` against `K_value + 1`,
then split the lower side on `K_value`, and refute each off-band case with
`absurd h_after_rw (by decide)` — once you `rw [h]` into the bound, the
remaining inequality is a closed-numeric `66 ≤ 55` (or similar) that
`by decide` flatly contradicts.

Useful disjunction shaper:

```lean
-- worlds < N+1 → (worlds ≤ N-1 ∨ N ≤ worlds)
example (worlds N : Nat) (hLt : worlds < N + 1) : worlds ≤ N ∨ N ≤ worlds :=
  (Nat.lt_or_ge worlds N).imp Nat.le_of_lt_succ id
```

The "= 10" closer in the band is just `Nat.le_antisymm (Nat.le_of_lt_succ hLt) hGeTen`.

### Pattern 4: Modular arithmetic with bounded operands

Goal shape: `(a + N - b) % N = 0` with `a, b < N` ⇒ `a = b`. The divisibility
argument decomposes into "0 < (sum) < 2N, only multiple of N in that range
is N itself."

```lean
have hDvd : N ∣ (q + N - p) := Nat.dvd_of_mod_eq_zero hk_zero
have hpLeQN : p ≤ q + N := Nat.le_trans (Nat.le_of_lt hp) (Nat.le_add_left N q)
have hPos  : 0 < q + N - p := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le hp (Nat.le_add_left N q))
have hLt2N : q + N - p < 2 * N := by
  -- left as exercise; bound q + N < N + N = 2N, then sub_le.
  ...
obtain ⟨k, hkEq⟩ := hDvd
-- k must be 1: k = 0 ⇒ q + N - p = 0 (contradicts hPos);
-- k ≥ 2 ⇒ q + N - p ≥ 2N (contradicts hLt2N).
have hkOne : k = 1 := ...
rw [hkOne, Nat.mul_one] at hkEq
-- hkEq : q + N - p = N. Add p to both sides; cancel.
have : q + N = p + N := by
  have hAdd : (q + N - p) + p = N + p := by rw [hkEq]
  rw [Nat.sub_add_cancel hpLeQN] at hAdd
  rw [hAdd, Nat.add_comm N p]
exact (Nat.add_right_cancel this).symm
```

The supporting lemmas are `Nat.dvd_of_mod_eq_zero`, `Nat.sub_pos_of_lt`,
`Nat.add_right_cancel`. Worked example: `helix55_encode_decode` in
`Gnosis/Helix55Dictionary.lean`.

For the simpler `(i + N) % N = i` case (`i < N`), use
`Nat.add_mod_right` followed by `Nat.mod_eq_of_lt hi`.

### Pattern 5b: Reflexive goals — when the hypothesis IS the goal

If you still see `theorem foo (h : P) : P := by omega`, the body was only
re-deriving `P` from `P` — replace with `:= h` (or `exact h`). The
`Gnosis/Dewey*ThinTopology.lean` sweep collapsed ~80 proofs of this shape to
term-mode; `omega` has no role in the finished proof.

Companion micro-patterns from the same files:

| Goal | Hypothesis | Replacement |
|---|---|---|
| `x = 0` | `h : x = nodes * 0` | `h.trans (Nat.mul_zero nodes)` |
| `x = y` | `h : x = y * 1` | `h.trans (Nat.mul_one y)` |
| `x ≥ y` | `h : x = y + z` | `h ▸ Nat.le_add_right y z` |
| `x ≤ y` | `h : x = y - z` | `h ▸ Nat.sub_le y z` |
| `n ≥ 0` | (anything) | `Nat.zero_le _` (drop the trivial hypothesis) |
| `parser + m ≥ parser` | `h : m ≥ 0` | `Nat.le_add_right parser m` (h is unused) |

If you see `theorem foo (h : trivial_for_Nat) : ...` and the proof still uses
an arithmetic tactic, the hypothesis is probably noise. Mark it `_h` and use
the structural lemma.

### Pattern 5: `iterateSucc`-style period lemmas

`iterateSucc n (m + 1) i = (i + 1 + m) % n` is provable by induction on
`m`. The recurring shape inside the proof is `(x % n + (1 + k)) % n =
(x + (1 + k)) % n`, which is `mod_add_left` (or `add_mod_right` for the
mirror). Both are one-line `rw` chains:

```lean
private theorem mod_add_left (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
```

### Pattern 5c: Polynomial expansion `(n+1)(b+1) = n*b + n + b + 1`

For a single-step factorization (helper lemmas like
`succ_succ_add_le_mul_succ` in `Gnosis/PipelineSpeedup.lean`):

```lean
have hexp : (n + 1) * (b + 1) = n * b + n + b + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
  simp [Nat.mul_one, Nat.one_mul]
  ac_rfl  -- handles the residual reordering
```

When the next step needs `(n+1)+(b+1) ≤ (n+1)*(b+1) + 1`, chain via
`calc` with `Nat.le_add_left` between two `ac_rfl` rearrangements:

```lean
calc (n + 1) + (b + 1)
    = n + b + 2 := by ac_rfl
  _ ≤ n * b + (n + b + 2) := Nat.le_add_left _ _
  _ = n * b + n + b + 1 + 1 := by
      rw [show (2 : Nat) = 1 + 1 from rfl]; ac_rfl
```

`ac_rfl` doesn't split numeric literals, so reify `2 = 1 + 1` (or
`3 = 1 + 1 + 1` etc.) before invoking it.

### Pattern 5d: Bounded division `(n * a) / b ≤ n` (with `a ≤ b`)

`(n * 3) / 4 ≤ n`, the `shrinkStep` shape from
`Gnosis/IteratedBizarroShrink.lean`:

```lean
calc (n * 3) / 4
    ≤ (n * 4) / 4 := Nat.div_le_div_right
        (Nat.mul_le_mul_left n (by decide : (3 : Nat) ≤ 4))
  _ = n := Nat.mul_div_cancel n (by decide : 0 < 4)
```

Generalisation: when you have a quotient bounded by a constant ratio,
inflate the dividend until the divisor cancels exactly, then collapse.

### Pattern 5e: Divisibility-strict `obtain ⟨k, rfl⟩` peeling

When you have `h : k ∣ n` and need to compute `n / k` exactly, peel `n`
to `k * j` and use `Nat.mul_div_cancel_left`:

```lean
unfold shrinkStep
obtain ⟨k, rfl⟩ := h  -- n becomes 4 * k
-- Goal: (4 * k * 3) / 4 * 4 = 4 * k * 3
rw [Nat.mul_assoc 4 k 3, Nat.mul_div_cancel_left (k * 3) (by decide : 0 < 4)]
ac_rfl
```

For the partner identity `4*k - k*3 = k`, peel `4*k` as `k*3 + k` first
(via `4 = 3 + 1` and `Nat.mul_add`), then `Nat.add_sub_cancel_left`:

```lean
rw [show 4 * k = k * 3 + k from by
      rw [Nat.mul_comm 4 k, show (4 : Nat) = 3 + 1 from rfl,
          Nat.mul_add, Nat.mul_one]]
exact Nat.add_sub_cancel_left (k * 3) k
```

### Pattern 6: Int-cast arithmetic over `Nat` differences

When a definition reads `def deficit (a b : Nat) : Int := (a : Int) - (b : Int)`
and you need an inequality on `deficit`, the recipe is:

1. **Reduce the goal to `Nat` form** by canceling Nat-cast layers via
   `Int.ofNat_le.mpr` / `Int.ofNat_lt.mpr`.
2. **Bridge `≤ 0` / `0 <`** with `Int.sub_nonpos_of_le` and
   `Int.sub_pos_of_lt`.
3. **Bridge `≤` between two diffs** with `Int.sub_le_sub_left` /
   `Int.sub_le_sub_right`.
4. **Cancel constants** like `((1 - 1 : Nat) : Int) = 0` via `rfl` then
   `Int.sub_zero`.

Example (`covering_match` from `CoveringSpaceCausality.lean`):

```lean
theorem covering_match
    (hMatch : pathCount ≤ transportStreams)
    (_hPathCount : 0 < pathCount) :
    topologicalDeficit pathCount transportStreams ≤ 0 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  -- (pathCount - 1) ≤ (transportStreams - 1) in Nat, cast to Int, then sub_nonpos.
  exact Int.sub_nonpos_of_le
    (Int.ofNat_le.mpr (Nat.sub_le_sub_right hMatch 1))
```

Strict version (`deficit_latency_separation`) uses `Int.ofNat_lt.mpr` plus
`Nat.sub_pos_of_lt`. Symmetric subtraction (`a - a = 0`) collapses with
`Int.sub_self`. The full set of lemma names that show up:

| Direction | Lemma |
|---|---|
| `a ≤ b → a - b ≤ 0` (Int) | `Int.sub_nonpos_of_le` |
| `b < a → 0 < a - b` (Int) | `Int.sub_pos_of_lt` |
| `a ≤ b → c - b ≤ c - a` (Int) | `Int.sub_le_sub_left` |
| Nat ≤ → Int ≤ | `Int.ofNat_le.mpr` |
| Nat < → Int < | `Int.ofNat_lt.mpr` |
| `((a : Nat) : Int) - ((a : Nat) : Int) = 0` | `Int.sub_self` |

### Pattern 7: godWeight / shifted-difference identity

When the goal is `(R - v + 1) - (R - (v + δ) + 1) = δ` (or any
shifted-difference identity from `godWeight R v - godWeight R (v + δ) = δ`),
the recipe is:

1. **Strip the `+1` cap** with `Nat.add_sub_add_right` — `(a + 1) - (b + 1) = a - b`.
2. **Distribute the inner subtraction** with `Nat.sub_add_eq R v δ` — `R - (v + δ) = R - v - δ`.
3. **Collapse with `Nat.sub_sub_self`** — `(R - v) - ((R - v) - δ) = δ`,
   which needs the side condition `δ ≤ R - v` (derive from `v + δ ≤ R`
   via `Nat.le_sub_of_add_le`).

Example (`adversarial_gap` in `Gnosis/AdversarialRobustness.lean`):

```lean
unfold godWeight
rw [Nat.min_eq_left hv, Nat.min_eq_left hD]
rw [Nat.add_sub_add_right]
rw [Nat.sub_add_eq R v delta]
have hdle : delta ≤ R - v :=
  Nat.le_sub_of_add_le (Nat.add_comm v delta ▸ hD)
exact Nat.sub_sub_self hdle
```

`adversarial_is_goodhart` (strict <) uses `Nat.sub_lt_sub_left` with the
extra `v_clean < R` hypothesis (derive via `Nat.lt_of_lt_of_le`), then
`Nat.add_lt_add_right (… ) 1` to re-introduce the `+1` shift.
`robust_training` (R-side monotonicity) uses `Nat.sub_lt_sub_right`.

The `robustness_floor : godWeight R v ≥ 1` is just `Nat.le_add_left 1 _` —
the `+1` clinamen is the floor.

### Pattern 8: Reflexive `Nat.ne_of_lt` after `rw [eq]`

When the goal is `x ≠ y` and you have `x = 0` (or `y = 0`) plus a positivity
hypothesis on the other side, *don't* destructure manually:

```lean
rw [h_eq]                  -- rewrites x to 0
exact Nat.ne_of_lt h_pos   -- 0 < y ⇒ 0 ≠ y
```

`Nat.ne_of_lt : a < b → a ≠ b`. Direction matters — if you have `y > 0`
and need `x ≠ y` after `rw`-ing `x = 0`, the result is `0 ≠ y`, which is
exactly `Nat.ne_of_lt h_pos`. **No `.symm` needed.** Used in
`distraction_is_destructive_interference` and
`attention_is_interference_system` (`AttentionAsConstructiveInterference`).

### Pattern 9: `simp only` with `if_neg`/`if_pos` to control branch shape

When `simp [definitionWithIf, hCond]` simplifies *too aggressively* (e.g.
deciding which side of a conjunction to keep), use surgical `simp only`:

```lean
simp only [chooseFailureAction, if_neg hKeep, if_pos hVent]
```

The conjunction shape is preserved. Then close each side with explicit
term-mode (`Nat.le_of_lt (Nat.lt_of_not_le …)`, etc.). Used in
`chosen_failure_action_coefficient_minimal`
(`Gnosis/FailureController.lean`) where `simp [..., hKeep]` was destroying
the `∧` before the proof could attack it.

### Hard shapes (still no `omega`)

These are the expensive Init-only shapes — not exceptions. Each one must close
with explicit lemmas (and lemma splits if the goal is still too wide):

- **Pure Int linear chains spanning multiple sub/neg ops without Nat-cast
  shortcuts.** Expect several lines per step. See `meta_truth_constancy`
  in `Gnosis/TopologicalMetabolism.lean` for the working pattern.
- **Free-variable search across two unfolds with mul + sub.** E.g.
  `Gnosis/BosonPosition.lean`'s `propagator_toward_sophia`.
- **Large `by_cases` cascades after `simp` over many boolean conditions.**
  Each branch can leave a free-variable linear residual after `simp`. The
  `by_cases h_cpu/h_gpu/h_npu/h_wasm` pattern in `Gnosis/HeteroMoAFabric.lean`
  is representative: every branch needs its own targeted Init-lemma chain —
  not a blanket arithmetic tactic at the end.
- **Nat-sub combinator** `(a₁ - b₁) + (a₂ - b₂) ≤ (a₁ + a₂) - (b₁ + b₂)`.
  See `composite_gap_lower_bound` in `Gnosis/BrunnianScanner.lean`.

## Why this matters

The `+1` is the clinamen. The Rustic Church doctrine is: every theorem
should compose cleanly from structural induction on `Nat.succ`. **`omega` is
disallowed entirely** — it is honest but opaque, and opacity is incompatible
with the doctrine. An explicit `Nat.sub_add_cancel h` makes the proof's *shape*
visible to the reader. When the algebra is built only from named inductive
lemmas, internal consistency reduces to "the kernel accepts the file", and the
formula's structure carries through every downstream theorem unchanged.

## Scope of this guide

This file is doctrine and proofcraft guidance only. It should answer:

- What proof surface counts as Rustic Church.
- Which tactics and imports are banned or conditionally allowed.
- Which Init-level lemmas close common proof shapes.
- How to split a stuck theorem into smaller Init-checkable facts.
- How to classify a claim as internal Lean proof, finite certificate, or
  external evidence.

This file is not a theorem backlog, module changelog, research notebook,
runtime design memo, strategy model, benchmark diary, or place to paste large
Lean examples. If a note is mainly about one module, put it in that module's
README or in the Lean file as a short comment. If it records future work, use
the relevant issue/task tracker. If it records a proof trick that generalizes,
distill the trick into the cookbook above and link the smallest checked module
that demonstrates it.

## Out of bounds and bridge discipline

Rustic Church does not try to replicate Mathlib's surface area. Direct
representations of continuous analysis, uncountable choice, infinite category
theory, large algebraic field machinery, or physical hardware truth are out of
scope unless they have been reframed as finite data and Init-level arithmetic.

The bridge rule is simple:

1. State the external claim as a named finite certificate or bounded witness.
2. Prove only the arithmetic consequence of that certificate inside Lean.
3. Keep empirical, physical, market, hardware, or deployment truth outside the
   theorem unless it is represented as explicit finite evidence.
4. Refuse prose that collapses external truth and internal proof into one
   claim.

Finite probability, finite stochastic processes, discrete refinement towers,
bounded runtime traces, and game/payoff tables can belong in `gnosis-math` when
their carrier is explicit and their theorem closes under this guide's tactic
rules. The guide should describe the discipline for those bridges; the detailed
inventory of bridged modules belongs near those modules.

## Documentation hygiene

When editing this file, remove scratch notes instead of expanding them. A good
addition is reusable across many proofs and can be checked against a small
Lean pattern. A bad addition is a status update, a one-off module narrative, a
large pasted theorem, or an empirical claim that has not been reduced to a
finite certificate boundary.

Before finishing any edit to this guide:

- Re-read the changed section and ask whether it teaches the approach or merely
  records work that happened.
- Keep examples short; link checked modules for detail.
- Preserve the hard bans: no Mathlib, no `omega`, no `simp`/`decide` on open
  arithmetic goals.
- Keep Layer C/external evidence visibly separate from kernel-checked Lean.
