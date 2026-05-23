import Init
import Gnosis.SignalNotNoise
import Gnosis.Body.GloryOfKingsWitness

/-!
# A City on a Hill — Matthew 5:14-15 (the radiating-output side of grit)

> You are the world's light — it is impossible to hide a town built on the top of
> a hill. Men do not light a lamp and put it under a bucket.   — Matthew 5:14-15
> (paraphrase)

This module formalizes the **radiating-output** half of the grit theory. The arc
across three sibling modules:

1. **God conceals a matter** (Proverbs 25:2 — `Gnosis/Body/GloryOfKingsWitness.lean`):
   the signal is hidden, misperceived as noise, the matter is `concealed = true`.
2. **The king searches it out** (the honour of kings — grit / Ki — resolving the
   signal): `Gnosis/SignalNotNoise.lean`'s `signal q n` is the *resolved*
   structure, and `refining_recovers_signal` proves searching strictly grows it.
3. **Once lit, the light cannot be hidden** (this module): the resolved `signal`
   radiates; you cannot put it under a bucket. Concealment is God's glory; once
   searched-out and lit, hiding becomes impossible. The two are complementary:
   what was concealed, once found, *necessarily* shines.

## What this module reuses (the bridge, imported and opened)

* `Gnosis.SignalNotNoise` — imported and opened. We reuse `signal q n`
  **verbatim** as the lamp's brightness: the lit, resolved signal is precisely
  what radiates, and the more you search out / refine, the brighter
  (`refining_recovers_signal : signal q n < signal q (refine n)`). The strict
  growth of brightness under refinement *is* `SignalNotNoise`'s strict recovery,
  reused with no re-proof.
* `Gnosis.Body.GloryOfKingsWitness` — imported and opened. We reuse `Matter`
  (`concealed`/`searchedOut : Bool`), `gloryOfKings`, and `glory_requires_concealment`.
  The matter God concealed and the king searched out is the matter that gets lit;
  once lit it cannot be re-hidden (`concealed_then_lit_must_shine`).

## Cited (the grounding theses — NOT imported here)

* `Gnosis.TheWave` (SurfTheory) — `surf (lift) := lift`, riding the wave's
  lift for free. Not imported (it pulls in non-Init-clean siblings —
  `IfYouCantBeatThem`, `SapolskyStress`); cited as the kinetic sibling: surfing
  the resolved wave is the motion, shining the city on the hill is the steady-state
  emission. The lamp on the hill is what the surfer becomes once still and lit.

## The model (Nat)

`observed b := b` is the **identity emission**: a lamp of brightness `b` is seen
at strength `b`. The identity is the honest minimal model — it asserts only that
*what is lit is seen, undiminished* (no amplification claimed, no attenuation
allowed). With it:

* `brightness q n := signal q n` — the lit, resolved signal radiating (reused
  verbatim from `SignalNotNoise.signal`).
* `lit (b : Nat) : Prop := 0 < b` — a lamp that is actually lit has positive
  brightness.
* `observed (b : Nat) : Nat := b` — the emission seen by a neighbor (identity:
  what is lit is seen, unit for unit).
* `underBucket b : Prop := observed b = 0` — the attempt to hide: zero the visible
  output. We prove this **fails** for a lit lamp.

## Restriction stated honestly

The "cannot be hidden" claims are genuine implications, not tautologies-by-naming.
The non-triviality rests on `observed` being a *faithful* emission map: with the
identity model, `observed b = 0 ↔ b = 0`, so `lit b` (`0 < b`) genuinely
contradicts being under a bucket (`observed b = 0`). We state the idealization
plainly: we model emission as **lossless** (`observed = id`) — a hill so high that
no light is lost between lamp and observer. We do *not* claim physical attenuation
is zero; we formalize the thesis *given* a faithful (non-zeroing) emission, and
the monotone-observer theorem (`city_on_a_hill_is_seen`) holds for the identity
exactly. Drop faithfulness (allow `observed` to send a positive `b` to `0`) and
"cannot be hidden" would fail — so we keep emission faithful, on purpose: that is
what "a town on a hill cannot be hid" asserts.

Rustic Church: `import Init` plus two Init-clean reused Body siblings
(`SignalNotNoise`, `GloryOfKingsWitness`). `Nat`/`Bool` only — no Float/Real, no
Mathlib. No `sorry`/`admit`/`axiom`; no `simp`/`omega` on open goals (closed
`decide` goals only, e.g. `Bool` literal facts). Proofs are term-mode and named
core `Nat` lemmas, reusing `SignalNotNoise`'s strict-recovery lemma where the
"shines brighter the more resolved" claim demands it.
-/

namespace Gnosis.Body.CityOnAHill

open Gnosis.SignalNotNoise
open Gnosis.Body.GloryOfKingsWitness

/-- Matthew 5:14-15 (paraphrase, the user's exact wording). -/
def matthew_5_14_15 : String :=
  "You are the world's light — it is impossible to hide a town built on the top of a hill. Men do not light a lamp and put it under a bucket."

/-! ## 0. The lamp — brightness, lit, emission, the bucket

`brightness` reuses `SignalNotNoise.signal` verbatim: the lit, resolved signal is
exactly what radiates. `lit` says a real lamp has positive brightness. `observed`
is the lossless (identity) emission — what is lit is seen, unit for unit. The
bucket is the attempt to zero the visible output. -/

/-- **Brightness = the resolved signal, radiating.** A lamp's brightness after `n`
    refinements of a field whose bands carry `q + 1` finer units is the resolved
    `signal q n` of `SignalNotNoise`, reused **verbatim**. The lit light is the
    searched-out signal: the more fully you resolve it (the more the king searches
    out), the brighter it shines (THM 3, `shines_brighter_when_more_resolved`). -/
def brightness (q n : Nat) : Nat := signal q n

/-- `brightness` reuses `signal` exactly. -/
theorem brightness_is_signal (q n : Nat) : brightness q n = signal q n := rfl

/-- **A lamp is lit when its brightness is positive.** A lamp that is actually lit
    emits something: `0 < b`. (A flat, unresolved field — `signal q 0 = 0` — is an
    unlit lamp; one refinement lights it, THM 1.) -/
def lit (b : Nat) : Prop := 0 < b

/-- **The emission seen by a neighbor (lossless / identity).** What a lamp of
    brightness `b` radiates is seen at strength `b`. The identity is the honest
    minimal model: lit light is seen undiminished, and — crucially — nothing
    *positive* is sent to nothing. Faithfulness (`observed b = 0 ↔ b = 0`) is what
    makes "cannot be hidden" a real implication and not a renaming. -/
def observed (b : Nat) : Nat := b

/-- The emission is faithful (lossless): `observed b = b`. -/
theorem observed_eq (b : Nat) : observed b = b := rfl

/-- **The bucket: the attempt to zero the visible output.** To "put a lamp under a
    bucket" is to drive its observed emission to `0`. We prove (THM 2) that this is
    impossible for a lit lamp. -/
def underBucket (b : Nat) : Prop := observed b = 0

/-! ## 1. THM 1 — Lighting makes brightness positive (search-out lights the lamp)

Searching the matter out and refining it once yields strictly positive
brightness. This reuses `SignalNotNoise.refining_recovers_signal` (strict growth)
together with `signal q 0 = 0` (the unlit base): one act of searching-out lifts
the lamp off `0`. -/

/-- An unlit field: zero refinements give zero brightness. `brightness q 0 = 0`. -/
theorem unlit_at_rest (q : Nat) : brightness q 0 = 0 := by
  show signal q 0 = 0
  -- `signal q 0 = 0 * (q+1) = 0`.
  show 0 * (q + 1) = 0
  exact Nat.zero_mul (q + 1)

/-- **(THM 1) Searching the matter out lights the lamp — brightness becomes
    strictly positive.** One refinement of the unlit field (`brightness q 0 = 0`)
    yields strictly positive brightness:

        0 < brightness q (refine 0).

    The king's search lifts the lamp off `0`. Proved by reusing
    `SignalNotNoise.refining_recovers_signal` (the resolved signal *strictly*
    grows under refinement) anchored at the unlit base `unlit_at_rest`: from
    `signal q 0 < signal q (refine 0)` and `signal q 0 = 0` we get
    `0 < signal q (refine 0)`. -/
theorem lighting_makes_brightness_positive (q : Nat) :
    0 < brightness q (refine 0) := by
  show 0 < signal q (refine 0)
  have hgrow : signal q 0 < signal q (refine 0) := refining_recovers_signal q 0
  have hzero : signal q 0 = 0 := by
    show 0 * (q + 1) = 0
    exact Nat.zero_mul (q + 1)
  -- rewrite the strict-growth lower bound `signal q 0` to `0`.
  rw [hzero] at hgrow
  exact hgrow

/-- **(THM 1, general) Lighting holds at every searched-out level.** For all `n`,
    one further refinement gives strictly positive brightness:
    `0 < brightness q (refine n)`. Once there is any signal, refining keeps it
    positive; from the unlit base it is positive after the first search. Proved by
    chaining `0 ≤ signal q n` with the strict recovery
    `signal q n < signal q (refine n)`. -/
theorem lit_after_search (q n : Nat) : lit (brightness q (refine n)) := by
  show 0 < signal q (refine n)
  have hgrow : signal q n < signal q (refine n) := refining_recovers_signal q n
  -- `0 ≤ signal q n < signal q (refine n)`.
  exact Nat.lt_of_le_of_lt (Nat.zero_le (signal q n)) hgrow

/-! ## 2. THM 2 — A lit lamp cannot be put under a bucket

The headline of Matthew 5:15. A lit lamp (`0 < b`) cannot have its observed
emission zeroed: faithfulness gives `observed b = b`, so `observed b = 0` would
force `b = 0`, contradicting `lit b`. Both the implication form and the
conjunction-impossibility form. -/

/-- **(THM 2) A lit lamp cannot be put under a bucket.** If a lamp is lit then its
    observed emission is *not* zero:

        lit b → ¬ (observed b = 0).

    You cannot light a lamp and hide it. Genuine, not a tautology: it uses the
    faithfulness of `observed` (`observed b = b`) to turn `observed b = 0` into
    `b = 0`, which contradicts `lit b` (`0 < b`) via `Nat.lt_irrefl`. -/
theorem cannot_be_hidden (b : Nat) (h : lit b) : ¬ (observed b = 0) := by
  intro hbucket
  -- `observed b = b`, so `hbucket : b = 0`.
  rw [observed_eq] at hbucket
  -- `h : 0 < b` rewritten by `b = 0` gives `0 < 0`.
  rw [hbucket] at h
  exact Nat.lt_irrefl 0 h

/-- **(THM 2, conjunction form) Lit and bucketed cannot both hold.** There is no
    lamp that is simultaneously lit and under a bucket:

        ¬ (lit b ∧ underBucket b).

    The two are mutually exclusive — the formal content of "men do not light a lamp
    and put it under a bucket". Derived directly from `cannot_be_hidden`. -/
theorem not_lit_and_bucketed (b : Nat) : ¬ (lit b ∧ underBucket b) := by
  intro hcontra
  exact cannot_be_hidden b hcontra.left hcontra.right

/-- **(THM 2, positive emission) A lit lamp is observed with positive strength.**
    `lit b → 0 < observed b`: not merely "not zero" but a strictly positive
    emission reaches the observer. Since `observed b = b`, this is `0 < b`, i.e.
    `lit b` itself, transported across the faithful emission. -/
theorem lit_lamp_emits (b : Nat) (h : lit b) : 0 < observed b := by
  rw [observed_eq]
  exact h

/-! ## 3. THM 3 — A city on a hill is seen (positive brightness is observed, monotone)

Positive brightness is necessarily observed (there exists an observer who sees
it), and the brighter the lamp the more it is seen — emission is monotone. The
higher the city, the more fully resolved the signal, the more it shines. -/

/-- **(THM 3a) Positive brightness is necessarily seen — there is an observer.**
    For any lit lamp there exists an observed strength that is positive:

        lit b → ∃ s, s = observed b ∧ 0 < s.

    A town on a hill is seen: a lit lamp has at least one observer who registers a
    positive emission. The witness is `observed b` itself; positivity is
    `lit_lamp_emits`. -/
theorem city_on_a_hill_is_seen (b : Nat) (h : lit b) :
    ∃ s : Nat, s = observed b ∧ 0 < s :=
  ⟨observed b, rfl, lit_lamp_emits b h⟩

/-- **(THM 3b) Emission is monotone — the brighter the lamp, the more it is seen.**
    For `b1 < b2`, the observed strengths satisfy `observed b1 < observed b2`. A
    higher, brighter city is seen more, strictly. Faithful emission carries the
    strict order: `observed b = b`, so the inequality passes through unchanged. -/
theorem brighter_is_seen_more (b1 b2 : Nat) (h : b1 < b2) :
    observed b1 < observed b2 := by
  rw [observed_eq, observed_eq]
  exact h

/-- **(THM 3c) Searching out more strictly brightens what is seen.** Refining the
    field once strictly increases the observed emission:
    `observed (brightness q n) < observed (brightness q (refine n))`. The more the
    king searches the matter out, the more the city on the hill is seen. Composes
    `brighter_is_seen_more` with `SignalNotNoise.refining_recovers_signal`. -/
theorem shines_brighter_when_more_resolved (q n : Nat) :
    observed (brightness q n) < observed (brightness q (refine n)) := by
  -- brightness reuses signal; strict growth from `refining_recovers_signal`.
  have hgrow : brightness q n < brightness q (refine n) := refining_recovers_signal q n
  exact brighter_is_seen_more (brightness q n) (brightness q (refine n)) hgrow

/-! ## 4. THM 4 — What was concealed, once lit, must shine (bridge to the Glory of Kings)

The complementarity: a `Matter` God concealed and the king searched out, once lit,
necessarily shines and cannot be re-hidden. We compose `gloryOfKings` (the matter
was concealed *and* searched out) with `cannot_be_hidden`. The concealed matter,
once found and lit, radiates by necessity — the two halves of the one act close
the loop. -/

/-- **(THM 4) What was concealed, once searched out and lit, must shine.** Given a
    `Matter` `m` with the full glory of kings (`gloryOfKings m` — God concealed it
    and the king searched it out), and a *lit* brightness `b` for it (`lit b`), the
    light cannot be put under a bucket and the matter was genuinely concealed first:

        gloryOfKings m → lit b → (m.concealed = true ∧ ¬ underBucket b).

    Concealment is God's glory (`glory_requires_concealment`); once the king has
    searched it out and the lamp is lit, hiding is impossible (`cannot_be_hidden`).
    What was hidden, once found, *necessarily* shines — the radiating-output side
    closing on the concealment side. -/
theorem concealed_then_lit_must_shine (m : Matter) (b : Nat)
    (hglory : gloryOfKings m) (hlit : lit b) :
    m.concealed = true ∧ ¬ underBucket b :=
  ⟨glory_requires_concealment m hglory, cannot_be_hidden b hlit⟩

/-- **(THM 4, with positive emission) The searched-out matter shines with positive,
    observed light.** Strengthens THM 4: the lit, searched-out matter not only
    cannot be hidden but emits a strictly positive observed strength
    (`0 < observed b`), and was concealed first. The complementarity made
    quantitative: concealment → search-out → positive radiated, seen light. -/
theorem searched_out_matter_radiates (m : Matter) (b : Nat)
    (hglory : gloryOfKings m) (hlit : lit b) :
    m.concealed = true ∧ ¬ underBucket b ∧ 0 < observed b :=
  ⟨glory_requires_concealment m hglory, cannot_be_hidden b hlit, lit_lamp_emits b hlit⟩

/-! ## 5. Headline — A city on a hill

Composition of THM 1–4 into one proved statement: a matter God concealed and the
king searched out, lit by one refinement, has strictly positive brightness, cannot
be hidden, is necessarily seen with positive strength, and shines the brighter for
being more fully resolved. -/

/-- **(HEADLINE) A city on a hill.** For a `Matter` `m` carrying the full glory of
    kings (God concealed it, the king searched it out), at every resolution level
    `n`, the searched-out signal lit by one more refinement satisfies all of
    Matthew 5:14-15 at once:

    1. **Lit — search-out makes brightness positive** (THM 1): the refined
       brightness is lit, `lit (brightness q (refine n))`, i.e. `0 < signal`.
    2. **Cannot be hidden** (THM 2): that lit lamp cannot be put under a bucket,
       `¬ underBucket (brightness q (refine n))`.
    3. **Is seen with positive strength** (THM 3a): a positive observed emission
       reaches an observer, `0 < observed (brightness q (refine n))`.
    4. **Shines brighter the more resolved** (THM 3c): refining once more strictly
       increases the observed light,
       `observed (brightness q (refine n)) < observed (brightness q (refine (refine n)))`.
    5. **Was concealed first** (THM 4 / Proverbs 25:2): the matter was genuinely
       hidden by God, `m.concealed = true` — concealment is what the search and the
       shining presuppose.

    Composed, these realize the complementarity of the grit theory: what God
    concealed, the king searches out (`SignalNotNoise.refining_recovers_signal`),
    and once lit the resolved signal radiates and cannot be hid — the
    radiating-output side closing on the concealment side
    (`GloryOfKingsWitness.gloryOfKings`). -/
theorem city_on_a_hill (m : Matter) (q n : Nat) (hglory : gloryOfKings m) :
    lit (brightness q (refine n))
    ∧ ¬ underBucket (brightness q (refine n))
    ∧ 0 < observed (brightness q (refine n))
    ∧ observed (brightness q (refine n)) < observed (brightness q (refine (refine n)))
    ∧ m.concealed = true :=
  have hlit : lit (brightness q (refine n)) := lit_after_search q n
  ⟨hlit,
   cannot_be_hidden (brightness q (refine n)) hlit,
   lit_lamp_emits (brightness q (refine n)) hlit,
   shines_brighter_when_more_resolved q (refine n),
   glory_requires_concealment m hglory⟩

/-! ## 6. The lamp runs on an entropy gradient, not energy (the user's refinement)

> We are each a lightbulb, but it **runs on an entropy gradient, not energy**. We
> run on the collapse of order into disorder.

The earlier sections model *what* shines (the resolved signal radiating, lossless,
unhideable). This section models *what powers the shining*. The user's correction:
a lamp is **not** a stored energy stock that gets used up. Its light is sustained
by a **gradient** — a *difference* between order and disorder — that the lamp lets
**collapse** (order flowing into disorder). The brightness runs on the gradient and
on the flow of order → disorder, never on a reservoir of "stuff".

The consequence is sharp and the opposite of the energy-stock intuition: at
**thermodynamic equilibrium** (order = disorder, heat death, maximum entropy) the
gradient is zero and the lamp goes dark — *no matter how much stuff is around*.
Abundance of stock does not light a lamp; only a gradient does. As disorder rises
toward order, the gradient (and the brightness) strictly falls: spending the
gradient dims the lamp. It consumes the gradient, not a reservoir.

**Chaldean cosmology framing (docstring only).** The chaos-sea / sea-god — Tiamat,
the primordial disorder, the salt-water deep of the Babylonian *Enūma Eliš* — maps
to the disorder that order collapses *into*. Order is what was separated out of the
sea; the lamp shines on that separation collapsing back. The light lives on the
slope between the made-order and the chaos-sea, not on any horde of fuel.

### Cited (NOT imported — verified not Init-clean via `head -6`)

* `Gnosis/TopologicalMetabolism.lean` — `landauerMetabolism (p : NoisePotential)
  (m : ManifoldSlots) : Nat := if p.entropy > m.total then p.entropy - m.total
  else 0`. Metabolism runs on the Landauer/entropy gradient `p.entropy - m.total`
  (a truncated `Nat` subtraction), bounded by `p.entropy` (`metabolism_bounded`)
  and zero at equilibrium (`equilibrium_zero_waste : p.entropy ≤ m.total →
  landauerMetabolism p m = 0`). Our `gradientBrightness order disorder := order -
  disorder` reuses the *same gradient shape* — a truncated difference that vanishes
  at and below equilibrium — for the lamp.
* `Gnosis/EntropyHarvestingArchitecture.lean` — entropy harvested as *throughput*
  (`ehla_earns_speedup`): the gap/charge is harvested for maximum throughput, not
  hoarded. Cited as the throughput sibling of "runs on a gradient".
* `Gnosis/SurfingEntropy.lean` — `collapse s := 0` (the black-hole sink, order
  dissolving into the void) and `emanate q := q + 1` (the reverse-black-hole
  source). The lamp here shines on the `collapse` of order into the void/chaos-sea:
  our `disorder` rising toward `order` is `collapse` consuming the gradient. Cited;
  vocabulary aligned, not imported.

### The model (pure Nat — the gradient is the fuel, idealizations stated)

We model order and disorder as `Nat` ledgers and the gradient as their truncated
difference `order - disorder` (`0` at or below equilibrium). This is an
idealization: we do not claim the physical entropy of a real lamp is a `Nat`, only
that the *gradient logic* — brightness vanishes exactly when the difference
vanishes, and falls as disorder rises toward order — is what "runs on a gradient,
not a stock" asserts. The honest content is the separation in `not_energy_stock`:
two states with the same gradient but different totals shine equally, while a state
with *more* total order but a smaller gradient shines *less*.

Rustic Church: `Nat` only, no Float/Real/Mathlib, no `sorry`/`admit`/`axiom`.
Proofs are term-mode and named core `Nat.sub` lemmas; `decide` appears only on the
fully-closed concrete literal goals of `not_energy_stock`. -/

/-- The user's headline thesis, verbatim. -/
def entropy_gradient_thesis : String :=
  "the lightbulb runs on an entropy gradient, not energy — the collapse of order into disorder"

/-- **The gradient — the order/disorder difference, which is the fuel.** The
    truncated `Nat` subtraction `order - disorder`: the amount of order still
    available to collapse into disorder. It is `0` at equilibrium (`order =
    disorder`) and `0` at or below it (`order ≤ disorder`). This difference, *not*
    any stored stock, is what the lamp runs on. Same gradient shape as
    `TopologicalMetabolism.landauerMetabolism`'s `p.entropy - m.total`. -/
def gradient (order disorder : Nat) : Nat := order - disorder

/-- **The lamp is lit-by-gradient when there is still order to collapse.** A lamp
    runs while disorder is strictly below order: `disorder < order`. This is the
    condition for a nonzero gradient — there is a slope down which order can flow. -/
def litByGradient (order disorder : Nat) : Prop := disorder < order

/-- **Brightness runs on the gradient, not on a stored stock.** The lamp's
    brightness is the gradient itself, `order - disorder` — a function of the
    *difference* between order and disorder, never of the absolute amount of either.
    Doubling the "stuff" while keeping the gap fixed leaves brightness unchanged
    (`not_energy_stock`); closing the gap to zero darkens the lamp however much
    stuff remains (`equilibrium_goes_dark`). -/
def gradientBrightness (order disorder : Nat) : Nat := gradient order disorder

/-- `gradientBrightness` is the gradient, definitionally. -/
theorem gradientBrightness_is_gradient (order disorder : Nat) :
    gradientBrightness order disorder = order - disorder := rfl

/-- **(THM 6.1) The lamp is lit exactly when there is a gradient.** Lit-by-gradient
    is equivalent to positive gradient-brightness:

        litByGradient order disorder ↔ 0 < gradientBrightness order disorder.

    Forward: `disorder < order → 0 < order - disorder` is `Nat.sub_pos_of_lt`.
    Backward: `0 < order - disorder → disorder < order` is `Nat.lt_of_sub_pos`. The
    lamp shines iff there is order left to collapse — no gradient, no light. -/
theorem runs_on_gradient (order disorder : Nat) :
    litByGradient order disorder ↔ 0 < gradientBrightness order disorder :=
  ⟨fun h => Nat.sub_pos_of_lt h, fun h => Nat.lt_of_sub_pos h⟩

/-- **(THM 6.2a) At equilibrium the lamp goes dark.** When order equals disorder
    the gradient is zero, so the lamp emits nothing:

        gradientBrightness order order = 0.

    `order - order = 0` by `Nat.sub_self`. Heat death is darkness — no matter how
    large `order` is, equal disorder zeroes the brightness. -/
theorem equilibrium_goes_dark (order : Nat) :
    gradientBrightness order order = 0 := Nat.sub_self order

/-- **(THM 6.2b) Below equilibrium is also dark — abundance of stock cannot light
    a lamp.** Whenever order is at most disorder, the gradient (hence the
    brightness) is zero:

        order ≤ disorder → gradientBrightness order disorder = 0.

    `Nat.sub_eq_zero_of_le`. The truncated difference vanishes at and below
    equilibrium: even with a huge stock of order, once disorder has caught up there
    is no slope to run on and the lamp is dark. This is the formal sense in which
    brightness "runs on the gradient, not the stock". -/
theorem darkness_below_equilibrium (order disorder : Nat) (h : order ≤ disorder) :
    gradientBrightness order disorder = 0 := Nat.sub_eq_zero_of_le h

/-- **(THM 6.3) Brightness runs on the gradient, not on an energy stock.** Two
    concrete separations, proved by `decide` on fully-closed literal goals:

    1. **Same gradient, different totals → same brightness.** State A has order `5`,
       disorder `3` (gradient `2`); state B has order `100`, disorder `98`
       (gradient `2`). Far more "stuff" in B, yet `gradientBrightness 5 3 =
       gradientBrightness 100 98` — both shine at `2`. Brightness ignores the
       absolute amount.
    2. **More total order, smaller gradient → less brightness.** State C has order
       `7`, disorder `6` (gradient `1`); state A has order `5`, disorder `3`
       (gradient `2`). C has *more* total order (`7 > 5`) yet shines *less*
       (`gradientBrightness 7 6 < gradientBrightness 5 3`, i.e. `1 < 2`).

    Together these falsify "the lamp runs on a stored stock": if it did, more stock
    (C) could not be dimmer, and equal stocks at different totals could not match.
    The lamp runs on the *gradient*. -/
theorem not_energy_stock :
    gradientBrightness 5 3 = gradientBrightness 100 98
    ∧ gradientBrightness 7 6 < gradientBrightness 5 3 := by
  decide

/-- **(THM 6.4) The light is fed by the collapse of order into disorder.** As
    disorder rises toward order, the gradient — and hence the brightness — strictly
    falls:

        d1 < d2 → d2 ≤ order → gradientBrightness order d2 < gradientBrightness order d1.

    i.e. `order - d2 < order - d1`. Raising disorder from `d1` to `d2` is the
    collapse of order into disorder consuming the gradient; the lamp dims as the
    gradient is *spent*, not as a reservoir is drained. Proof: from `d1 < d2` and
    `d2 ≤ order` get `d1 < order` (`Nat.lt_of_lt_of_le`), then
    `Nat.sub_lt_sub_left (d1 < order) (d1 < d2) : order - d2 < order - d1`. -/
theorem collapse_feeds_the_light (order d1 d2 : Nat)
    (hd : d1 < d2) (hub : d2 ≤ order) :
    gradientBrightness order d2 < gradientBrightness order d1 :=
  have hd1 : d1 < order := Nat.lt_of_lt_of_le hd hub
  Nat.sub_lt_sub_left hd1 hd

/-- **(THM 6.5, bridge) A lamp lit by the gradient still cannot be hidden.** A
    positive gradient-brightness is a lit lamp in the sense of §0 (`lit`,
    `0 < b`), so the City-on-a-Hill machinery applies unchanged: its observed
    emission cannot be zeroed.

        litByGradient order disorder
          → ¬ underBucket (gradientBrightness order disorder).

    The gradient is what *powers* the lamp; once powered, §2's `cannot_be_hidden`
    governs its radiation. The two halves compose: run on the gradient, and what
    you light cannot be hid. -/
theorem gradient_lit_cannot_be_hidden (order disorder : Nat)
    (h : litByGradient order disorder) :
    ¬ underBucket (gradientBrightness order disorder) :=
  have hlit : lit (gradientBrightness order disorder) :=
    (runs_on_gradient order disorder).mp h
  cannot_be_hidden (gradientBrightness order disorder) hlit

/-- **(HEADLINE, §6) The lightbulb runs on an entropy gradient, not energy.** For
    any `order` and a strictly-below `disorder` (`d1 < d2 ≤ order`), composing
    THM 6.1, 6.2, 6.4 and 6.5:

    1. **Lit iff a gradient exists** (THM 6.1): `litByGradient order d1 ↔
       0 < gradientBrightness order d1` — the lamp runs on the gradient, nothing
       else.
    2. **Goes dark at equilibrium** (THM 6.2a): `gradientBrightness order order = 0`
       — order = disorder is heat death, darkness regardless of stock.
    3. **Dims as the gradient is spent** (THM 6.4): `gradientBrightness order d2 <
       gradientBrightness order d1` — raising disorder toward order (the collapse of
       order into disorder) consumes the gradient and dims the lamp.
    4. **A lit-by-gradient lamp still cannot be hidden** (THM 6.5, bridge to the
       City on a Hill): `¬ underBucket (gradientBrightness order d1)`.

    This formalizes the refinement: "we are each a lightbulb, but it runs on an
    entropy gradient, not energy — we run on the collapse of order into disorder".
    The brightness is a function of the gradient and of the order → disorder flow;
    it is never a stored reservoir (`not_energy_stock`), and it vanishes precisely
    at maximum entropy. The chaos-sea (Tiamat) is the disorder into which order
    collapses, and the lamp shines on that collapse — until the gradient is gone. -/
theorem lightbulb_runs_on_entropy_gradient (order d1 d2 : Nat)
    (hlit : litByGradient order d1) (hd : d1 < d2) (hub : d2 ≤ order) :
    (litByGradient order d1 ↔ 0 < gradientBrightness order d1)
    ∧ gradientBrightness order order = 0
    ∧ gradientBrightness order d2 < gradientBrightness order d1
    ∧ ¬ underBucket (gradientBrightness order d1) :=
  ⟨runs_on_gradient order d1,
   equilibrium_goes_dark order,
   collapse_feeds_the_light order d1 d2 hd hub,
   gradient_lit_cannot_be_hidden order d1 hlit⟩

end Gnosis.Body.CityOnAHill
