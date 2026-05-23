import Init
import Gnosis.Body.DiversityIsOptimal
import Gnosis.Body.AmnesiaGritFrontier
import Gnosis.Body.SapolskyStress

/-!
# Societal Resilience — Diversity Is Good, But Has Limits (the Inverted-U Frontier)

`Gnosis.Body.DiversityIsOptimal` proves the *lower* claim: under uncertainty,
diversity beats monoculture — a population with zero diversity (`d = 0`) is a
brittle specialist whose worst case is `0`. That module establishes the LEFT
edge of the curve: too little diversity is fatal.

This module adds the half that `DiversityIsOptimal` deliberately left open: the
*upper* limit. Diversity is not a free good to be maximized without bound.
Beyond some point, more diversity stops buying adaptability and starts dissolving
the **shared base** — the common infrastructure, language, institutions, and
cohesion a society needs to coordinate at all. At the extreme `d = maxDiversity`
there is no shared base left, so a fully fragmented society cannot act in concert
and is *also* fatal — for the opposite reason to the monoculture.

So societal resilience is an **inverted-U** in diversity, exactly the dose-response
shape of `Gnosis.Body.SapolskyStress.inverted_u` (the dose makes the poison) and
the Pareto tension of `Gnosis.Body.AmnesiaGritFrontier.frontier_principle` (grit
vs. adaptability). Two opposing goods that diversity cannot maximize together:

* **adaptability** `adaptability d = d` — rises with diversity (the
  `DiversityIsOptimal` good: more variants to select from when the world shifts);
* **cohesion**     `cohesion d maxDiversity = maxDiversity - d` — *falls* with
  diversity (the new constraint: a wider spread thins the shared base).

Resilience needs BOTH, so we take their product (a discrete Cobb-Douglas / `Nat`
parabola, structurally identical to `SapolskyStress.performance`):

    societalResilience d maxDiversity := d * (maxDiversity - d)
                                       = adaptability d * cohesion d maxDiversity.

It is `0` at both extremes — brittle monoculture (`d = 0`, no adaptability) and
total fragmentation (`d = maxDiversity`, no cohesion) — and strictly higher in
between. The robust society is *interior*: diverse enough to adapt, cohesive
enough to coordinate.

**Dietary diversity** (`vegan_omnivore_diversity_instance`) is a concrete reading
of the same `d`: a population that eats exactly one way (all-omnivore, all-vegan)
is brittle to a crop / supply failure in its single base; a population with no
shared dietary base at all loses its common food infrastructure. The healthy
state is a mix — some diversity, but on a shared base.

Rustic Church: `import Init` only, plus the three `Init`-clean sibling Body
modules above (imported and `open`ed to bridge their facts directly). `Nat`
arithmetic only — no Float, no Real, no Mathlib. No `sorry`; no
`simp`/`decide`/`omega` on open goals. Proofs run on core `Nat` lemmas and on the
already-proven `SapolskyStress` inverted-U arms.
-/

namespace Gnosis.Body.SocietalResilience

open Gnosis.Body.DiversityIsOptimal
open Gnosis.Body.AmnesiaGritFrontier
open Gnosis.Body.SapolskyStress

/-! ## 1. The two opposing goods diversity cannot maximize together

`adaptability` is the `DiversityIsOptimal` good — more diversity, more variants
to field when the environment shifts. `cohesion` is the new constraint this
module contributes — the shared base (common infrastructure, language,
institutions) that thins as diversity widens. Their tension is the whole point:
you cannot push `d` up to gain adaptability without spending cohesion. -/

/-- **Adaptability rises with diversity.** The `DiversityIsOptimal` good measured
    on the diversity axis: a more diverse society has more variants to select
    from when the world changes, so adaptability is just the diversity `d`. -/
def adaptability (d : Nat) : Nat := d

/-- **Cohesion falls with diversity.** The shared base — common infrastructure,
    language, institutions, the "us" a society coordinates through — out of a
    maximal base `maxDiversity`, thinned by every unit of spread: `maxDiversity - d`
    (truncated subtraction). This is the constraint `DiversityIsOptimal` left
    open: diversity is not free, it is spent against cohesion. -/
def cohesion (d maxDiversity : Nat) : Nat := maxDiversity - d

/-- **Adaptability is non-decreasing in diversity.** More diversity never means
    less adaptability — the rising side of the Pareto tension. -/
theorem adaptability_nondecreasing (d1 d2 : Nat) (h : d1 ≤ d2) :
    adaptability d1 ≤ adaptability d2 := by
  unfold adaptability
  exact h

/-- **Cohesion is non-increasing in diversity.** More diversity never means more
    cohesion — the falling side of the Pareto tension. (`maxDiversity - d` is
    antitone in `d`.) -/
theorem cohesion_nonincreasing (d1 d2 maxDiversity : Nat) (h : d1 ≤ d2) :
    cohesion d2 maxDiversity ≤ cohesion d1 maxDiversity := by
  unfold cohesion
  exact Nat.sub_le_sub_left h maxDiversity

/-- **THE PARETO TENSION (theorem 4).** `adaptability_rises_cohesion_falls`: you
    cannot maximize both goods at once. For any strictly higher diversity
    `d1 < d2`, adaptability does not decrease while cohesion does not increase —
    every gain in adaptability is paid in shared base. This is the diversity-axis
    analogue of `AmnesiaGritFrontier.amnesia_grit_is_a_frontier` (grit vs.
    adaptability) and the reason resilience must sit at an interior point. -/
theorem adaptability_rises_cohesion_falls (d1 d2 maxDiversity : Nat) (h : d1 ≤ d2) :
    adaptability d1 ≤ adaptability d2 ∧
    cohesion d2 maxDiversity ≤ cohesion d1 maxDiversity :=
  ⟨adaptability_nondecreasing d1 d2 h,
   cohesion_nonincreasing d1 d2 maxDiversity h⟩

/-! ## 2. Societal resilience: the product needs BOTH goods

Resilience requires adaptability AND cohesion together — a society that can adapt
but cannot coordinate is as fragile as one that coordinates but cannot adapt. So
we multiply (a discrete Cobb-Douglas: the product is `0` the moment *either*
factor is `0`). The result is exactly `SapolskyStress.performance d maxDiversity`,
the inverted-U parabola, re-read on the diversity axis. -/

/-- **Societal resilience.** Adaptability times cohesion: a society is resilient
    only when it has *both* room to adapt and a shared base to coordinate through.
    A discrete downward parabola on `0..maxDiversity`, equal to
    `SapolskyStress.performance d maxDiversity`. -/
def societalResilience (d maxDiversity : Nat) : Nat :=
  adaptability d * cohesion d maxDiversity

/-- **Resilience is the product of the two goods**, by definition — the
    Cobb-Douglas reading made explicit. -/
theorem societalResilience_eq_product (d maxDiversity : Nat) :
    societalResilience d maxDiversity = adaptability d * cohesion d maxDiversity := rfl

/-- **Bridge to the Sapolsky inverted-U.** Societal resilience in diversity is
    *definitionally* `SapolskyStress.performance` in stress: the same discrete
    parabola `d * (maxDiversity - d)`. Everything proved about the inverted-U
    dose-response transfers verbatim to diversity. -/
theorem societalResilience_is_sapolsky_performance (d maxDiversity : Nat) :
    societalResilience d maxDiversity = performance d maxDiversity := by
  unfold societalResilience adaptability cohesion performance
  rfl

/-! ## 3. Both extremes fail — the lower edge and the NEW upper edge -/

/-- **Monoculture is brittle (theorem 1).** At `d = 0` — no diversity, the
    specialist monoculture of `DiversityIsOptimal` — societal resilience is `0`:
    a society with zero adaptability has nothing to select from when the world
    shifts. This is the LEFT edge, agreeing with
    `DiversityIsOptimal.monoculture_has_low_worst_case` and the `s = 0` comfort
    end of `SapolskyStress.zero_stress_zero_performance`. -/
theorem monoculture_is_brittle (maxDiversity : Nat) :
    societalResilience 0 maxDiversity = 0 := by
  unfold societalResilience adaptability
  exact Nat.zero_mul (cohesion 0 maxDiversity)

/-- **Total fragmentation fails (theorem 2 — the NEW upper limit).** At
    `d = maxDiversity` — maximal diversity, no shared base — societal resilience
    is *also* `0`: cohesion `maxDiversity - maxDiversity = 0`, so a fully
    fragmented society has nothing to coordinate through and cannot act in
    concert. This is the RIGHT edge that `DiversityIsOptimal` does not have — the
    honest upper bound on diversity, mirroring the `s = capacity` collapse end of
    `SapolskyStress.max_stress_zero_performance`. Too much diversity is as fatal
    as too little, for the opposite reason. -/
theorem total_fragmentation_fails (maxDiversity : Nat) :
    societalResilience maxDiversity maxDiversity = 0 := by
  unfold societalResilience cohesion
  rw [Nat.sub_self]
  exact Nat.mul_zero (adaptability maxDiversity)

/-- **Both extremes are fatal.** Monoculture (`d = 0`, no adaptability) and total
    fragmentation (`d = maxDiversity`, no cohesion) both yield zero resilience —
    the two ends of the inverted-U, for opposite reasons. -/
theorem both_extremes_fail (maxDiversity : Nat) :
    societalResilience 0 maxDiversity = 0 ∧
    societalResilience maxDiversity maxDiversity = 0 :=
  ⟨monoculture_is_brittle maxDiversity, total_fragmentation_fails maxDiversity⟩

/-! ## 4. The sweet spot is interior — resilience peaks in the middle -/

/-- **Resilience peaks in the middle (theorem 3).** `resilience_peaks_in_the_middle`:
    there is an *interior* diversity strictly more resilient than either extreme.
    Whenever the base is wide enough to have an interior at all
    (`2 ≤ maxDiversity`), the witness `d = 1` (some diversity, but not all) beats
    both endpoints:

        societalResilience 0 maxDiversity            < societalResilience 1 maxDiversity  ∧
        societalResilience maxDiversity maxDiversity < societalResilience 1 maxDiversity.

    The two extremes are `0` (`both_extremes_fail`), and at `d = 1` resilience is
    `1 * (maxDiversity - 1) = maxDiversity - 1 ≥ 1 > 0`. So the societal sweet
    spot is genuinely interior — diverse enough to adapt, cohesive enough to
    coordinate. This mirrors `SapolskyStress.inverted_u`: a peak with strictly
    lower values at the ends. -/
theorem resilience_peaks_in_the_middle (maxDiversity : Nat) (h : 2 ≤ maxDiversity) :
    societalResilience 0 maxDiversity < societalResilience 1 maxDiversity ∧
    societalResilience maxDiversity maxDiversity < societalResilience 1 maxDiversity := by
  -- interior value: societalResilience 1 = 1 * (maxDiversity - 1) = maxDiversity - 1.
  have hmid : societalResilience 1 maxDiversity = maxDiversity - 1 := by
    unfold societalResilience adaptability cohesion
    rw [Nat.one_mul]
  -- interior value is strictly positive: 1 ≤ maxDiversity - 1, since 2 ≤ maxDiversity.
  have hpos : 0 < societalResilience 1 maxDiversity := by
    rw [hmid]
    -- 0 < maxDiversity - 1  ⇐  1 < maxDiversity  ⇐  2 ≤ maxDiversity
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h)
  refine ⟨?_, ?_⟩
  · rw [monoculture_is_brittle maxDiversity]
    exact hpos
  · rw [total_fragmentation_fails maxDiversity]
    exact hpos

/-! ## 5. Concrete instance: dietary diversity (vegan / vegetarian / omnivore)

Read `d` as **dietary diversity** of a population on a `maxDiversity`-wide food
base. `d = 0` is a single uniform diet (all-omnivore, or all-vegan): brittle to a
crop / supply failure in its one base, with no fallback. `d = maxDiversity` is
maximal dietary spread with no shared base at all: the common food
infrastructure — shared crops, distribution, kitchens, knowledge — dissolves.
The healthy state is a *mix*: some diversity, on a shared base. This is a clean
instance of theorems 1–3 with `d` reinterpreted; no new model. -/

/-- **A fully uniform diet is brittle.** A population eating exactly one way
    (`dietDiversity = 0`) has zero dietary resilience: a single supply shock to
    its one base wipes it out, with nothing to fall back on. Instance of
    `monoculture_is_brittle`. -/
theorem uniform_diet_is_brittle (maxDiversity : Nat) :
    societalResilience 0 maxDiversity = 0 :=
  monoculture_is_brittle maxDiversity

/-- **A fully fragmented diet base fails too.** Maximal dietary spread with no
    shared base (`dietDiversity = maxDiversity`) loses the common food
    infrastructure — shared crops, distribution, kitchens, knowledge — so dietary
    resilience is *also* zero. Instance of `total_fragmentation_fails`: the upper
    limit on dietary diversity. -/
theorem fragmented_diet_fails (maxDiversity : Nat) :
    societalResilience maxDiversity maxDiversity = 0 :=
  total_fragmentation_fails maxDiversity

/-- **DIETARY DIVERSITY IS AN INVERTED-U (theorem 5).**
    `vegan_omnivore_diversity_instance`: a population needs *some* dietary
    diversity (vegan, vegetarian, omnivore in the mix — resilience to a crop /
    supply failure) but a fully fragmented diet base loses shared food
    infrastructure. So a uniform diet (`d = 0`) and a fully fragmented one
    (`d = maxDiversity`) are both brittle, while a *mix* (`d = 1`) is strictly
    more resilient than either. A clean instance of theorems 1–3 with `d` read as
    diet diversity. The optimum is a mix on a shared base — not uniformity, not
    total fragmentation. -/
theorem vegan_omnivore_diversity_instance (maxDiversity : Nat) (h : 2 ≤ maxDiversity) :
    -- uniform diet is brittle
    societalResilience 0 maxDiversity = 0 ∧
    -- fully fragmented diet base also fails (the upper limit)
    societalResilience maxDiversity maxDiversity = 0 ∧
    -- a mix is strictly more resilient than either extreme
    societalResilience 0 maxDiversity < societalResilience 1 maxDiversity ∧
    societalResilience maxDiversity maxDiversity < societalResilience 1 maxDiversity :=
  ⟨uniform_diet_is_brittle maxDiversity,
   fragmented_diet_fails maxDiversity,
   (resilience_peaks_in_the_middle maxDiversity h).left,
   (resilience_peaks_in_the_middle maxDiversity h).right⟩

/-! ## 6. The headline -/

/-- **Societal resilience is an inverted-U in diversity (the headline).**
    `societal_resilience_is_an_inverted_u` composes theorems 1–4 into one theory.
    Diversity is good for society — but it has LIMITS, and resilience peaks at an
    *intermediate* diversity, not at either extreme:

    * (lower edge — `monoculture_is_brittle`) at `d = 0` resilience is `0`: a
      brittle monoculture with no adaptability — the LEFT edge that
      `DiversityIsOptimal.monoculture_has_low_worst_case` already establishes;
    * (upper edge — `total_fragmentation_fails`) at `d = maxDiversity` resilience
      is *also* `0`: total fragmentation with no shared base — the NEW RIGHT edge
      this module adds beyond `DiversityIsOptimal`;
    * (interior peak — `resilience_peaks_in_the_middle`) some intermediate
      diversity is strictly more resilient than either extreme — the sweet spot is
      interior, mirroring `SapolskyStress.inverted_u`;
    * (Pareto tension — `adaptability_rises_cohesion_falls`) the reason: more
      diversity buys adaptability only by spending cohesion, so neither can be
      maximized alone — the diversity-axis form of
      `AmnesiaGritFrontier.frontier_principle`.

    Therefore the robust society sits at an interior frontier point: diverse
    enough to adapt, cohesive enough to coordinate. Bundled so the four claims are
    provably one theory — diversity is good, in the right dose. -/
theorem societal_resilience_is_an_inverted_u (maxDiversity : Nat) (h : 2 ≤ maxDiversity) :
    -- lower edge: monoculture is brittle (no adaptability)
    societalResilience 0 maxDiversity = 0 ∧
    -- upper edge: total fragmentation fails (no cohesion / shared base) — NEW limit
    societalResilience maxDiversity maxDiversity = 0 ∧
    -- interior peak: a middle diversity strictly beats both extremes
    (societalResilience 0 maxDiversity < societalResilience 1 maxDiversity ∧
     societalResilience maxDiversity maxDiversity < societalResilience 1 maxDiversity) ∧
    -- Pareto tension: adaptability up forces cohesion down (cannot maximize both)
    (∀ d1 d2 : Nat, d1 ≤ d2 →
      adaptability d1 ≤ adaptability d2 ∧
      cohesion d2 maxDiversity ≤ cohesion d1 maxDiversity) :=
  ⟨monoculture_is_brittle maxDiversity,
   total_fragmentation_fails maxDiversity,
   resilience_peaks_in_the_middle maxDiversity h,
   fun d1 d2 hd => adaptability_rises_cohesion_falls d1 d2 maxDiversity hd⟩

end Gnosis.Body.SocietalResilience
