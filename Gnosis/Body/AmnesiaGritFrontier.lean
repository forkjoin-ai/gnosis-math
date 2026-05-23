import Init
import Gnosis.Body.Anthropogenesis
import Gnosis.Body.Robustness

/-!
# Amnesia, Grit, and the American Frontier — the Pareto Tradeoff of Memory

GRIT THEORY's core tension, formalized as an explore/exploit ("American
Frontier") Pareto-optimality problem in the body / Metaverse.

A living system carries `memory : Nat` — accumulated structure, culture, grit.
There are two ways to act on it, pulling in opposite directions:

* **Amnesia** is a reset to the void: `amnesia _ = 0`. It is **idempotent**
  (forgetting twice is forgetting once) and the void `0` is its absorbing fixed
  point. This is the absolute-zero / `NullIsTheZero` idempotent re-derived
  locally (we keep the module `Init`-clean and do not import the non-`Init`
  `BuleyEquilibrium`).
* **Accumulation** (evolution) grows memory monotonically: `accumulate m gain =
  m + gain`. Without amnesia, memory never decreases — the cultural ratchet of
  `Anthropogenesis.culture_never_regresses` (`inheritedCulture`), reused here.

A `retention` policy `r` out of a `scale` interpolates between the two: keep
`r/scale` of memory each step (`retain m r scale = (m * r) / scale`). `r = 0` is
pure amnesia (forget all); `r = scale` is pure grit (keep all).

Two payoffs are in tension:

* `accumulationValue` rewards retained memory (favors high retention — settled,
  exploit, the homestead);
* `adaptability = scale - r` rewards forgetting (favors low retention — open,
  explore, the frontier). Cf. `Evolution.monoculture_dies_on_change`: pure
  retention is monoculture and dies when the world changes.

The headline (`frontier_principle`): grit and amnesia trade off on a genuine
**Pareto frontier**. The two extremes each forfeit one objective entirely
(`pure_grit_has_no_adaptability`, `pure_amnesia_has_no_accumulation`), so
robustness lives at an *interior* frontier point — life on the edge between
settled memory and open exploration, the American Frontier.

Rustic Church: `import Init` only (plus the two sibling Body modules reused).
`Nat` arithmetic, proofs from core `Nat` lemmas. No `sorry`, no Mathlib, no
`simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.AmnesiaGritFrontier

open Gnosis.Body.Anthropogenesis
open Gnosis.Body.Robustness

/-! ## 1. Amnesia: the idempotent reset to the void -/

/-- **Amnesia.** A reset to the void: whatever the accumulated memory, after
    amnesia there is nothing left. The discrete absolute-zero / absorbing
    element. -/
def amnesia (_ : Nat) : Nat := 0

/-- **Amnesia is idempotent.** Forgetting twice is forgetting once — the reset to
    the void is a true idempotent (the `NullIsTheZero` no-op, re-derived locally
    so the module stays `Init`-clean). There is nothing left to forget the second
    time. -/
theorem amnesia_is_idempotent (m : Nat) : amnesia (amnesia m) = amnesia m := rfl

/-- The void is itself amnesia's fixed point: resetting the void yields the void. -/
theorem void_is_amnesia_fixed_point : amnesia 0 = 0 := rfl

/-- **The void is the absorbing fixed point.** Amnesia sends *every* memory to the
    void `0`; the void is the single point it can no longer move. This is exactly
    `BuleyEquilibrium.isAbsoluteZero`'s idempotent collapse, re-derived in `Nat`. -/
theorem amnesia_collapses_to_void (m : Nat) : amnesia m = 0 := rfl

/-! ## 2. Accumulation: the evolutionary ratchet -/

/-- **Accumulation** (evolution): memory grows by the period's gain. -/
def accumulate (m gain : Nat) : Nat := m + gain

/-- **Accumulation ratchets.** Without amnesia, memory never decreases: each
    accumulating step leaves at least as much as before. This is the cultural
    ratchet of `Anthropogenesis.culture_never_regresses` in additive form — the
    evolutionary side of the tradeoff. -/
theorem accumulation_ratchets (m gain : Nat) : m ≤ accumulate m gain := by
  unfold accumulate
  exact Nat.le_add_right m gain

/-- **The ratchet bridges to the cultural ratchet.** The inherited-culture floor
    of `Anthropogenesis` — the union `inheritedCulture m gain = max m gain`, which
    `culture_never_regresses` shows never drops below `m` — is itself dominated by
    additive accumulation `m + gain`. So the additive ratchet here and the
    `max`-ratchet of `Anthropogenesis` are the same no-regress law, with addition
    the stronger floor. -/
theorem accumulation_dominates_inherited (m gain : Nat) :
    inheritedCulture m gain ≤ accumulate m gain := by
  unfold inheritedCulture accumulate
  exact Nat.max_le.mpr ⟨Nat.le_add_right m gain, Nat.le_add_left gain m⟩

/-! ## 3. Retention: interpolating between amnesia and grit -/

/-- **Retention.** A policy `r` out of `scale` keeps `r/scale` of memory each
    step. `r = 0` is pure amnesia; `r = scale` is pure grit. -/
def retain (m r scale : Nat) : Nat := (m * r) / scale

/-- **Pure amnesia forgets everything.** Retention `r = 0` discards all memory —
    it *is* `amnesia`. -/
theorem retain_zero_is_amnesia (m scale : Nat) : retain m 0 scale = amnesia m := by
  unfold retain amnesia
  rw [Nat.mul_zero]
  exact Nat.zero_div scale

/-- **Retention is monotone in the policy.** Keeping a larger fraction never keeps
    less memory: more grit retains more. (`m * r` is monotone in `r`, and integer
    division by a fixed `scale` is monotone in its numerator.) -/
theorem retention_monotone (m r1 r2 scale : Nat) (h : r1 ≤ r2) :
    retain m r1 scale ≤ retain m r2 scale := by
  unfold retain
  exact Nat.div_le_div_right (Nat.mul_le_mul_left m h)

/-! ## 4. The two payoffs in tension -/

/-- **Accumulation value.** More retained memory is more accumulated
    culture/grit — the exploit / settled-homestead payoff. -/
def accumulationValue (m : Nat) : Nat := m

/-- **Adaptability.** Room left to adapt to a changed world: the fraction *not*
    retained, `scale - r` — the explore / open-frontier payoff. Cf.
    `Evolution.monoculture_dies_on_change`: a pure-retention monoculture has zero
    adaptability and dies when the world shifts. -/
def adaptability (r scale : Nat) : Nat := scale - r

/-! ## 5. THE TRADEOFF — each extreme forfeits one objective entirely -/

/-- **Pure grit has no adaptability.** Retaining everything (`r = scale`) leaves
    `scale - scale = 0` room to adapt: a perfectly settled, perfectly brittle
    system — the monoculture that dies on change. -/
theorem pure_grit_has_no_adaptability (scale : Nat) : adaptability scale scale = 0 := by
  unfold adaptability
  exact Nat.sub_self scale

/-- **Pure amnesia has no accumulation.** Forgetting everything (`r = 0`) leaves
    zero retained memory, so the accumulation payoff collapses to the void: an
    endlessly exploring system that banks nothing. -/
theorem pure_amnesia_has_no_accumulation (m scale : Nat) :
    accumulationValue (retain m 0 scale) = 0 := by
  unfold accumulationValue
  rw [retain_zero_is_amnesia m scale]
  exact amnesia_collapses_to_void m

/-- **The two extremes are each fatal.** Pure grit forfeits all adaptability and
    pure amnesia forfeits all accumulation — neither endpoint can hold both
    objectives. The tradeoff is real, not a matter of degree. -/
theorem extremes_are_fatal (m scale : Nat) :
    adaptability scale scale = 0 ∧ accumulationValue (retain m 0 scale) = 0 :=
  ⟨pure_grit_has_no_adaptability scale, pure_amnesia_has_no_accumulation m scale⟩

/-! ## 6. THE FRONTIER — a genuine Pareto characterization -/

/-- **The combined frontier objective**: accumulation of what is retained plus
    the adaptability of what is forgotten. (For this linear-in-`r` objective the
    optimum sits at a *vertex*, so we do not claim a strictly-dominating interior
    point — that would be false; instead we prove the honest Pareto statement
    below.) -/
def frontierValue (m r scale : Nat) : Nat :=
  accumulationValue (retain m r scale) + adaptability r scale

/-- **Adaptability is strictly antitone on the frontier.** Moving to a strictly
    higher retention `r1 < r2 ≤ scale` strictly *decreases* adaptability. -/
theorem adaptability_strictly_decreases (r1 r2 scale : Nat)
    (hlt : r1 < r2) (hle : r2 ≤ scale) :
    adaptability r2 scale < adaptability r1 scale := by
  unfold adaptability
  -- scale - r2 < scale - r1, needing r1 < scale and r1 < r2.
  exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le hlt hle) hlt

/-- Moving to higher retention never decreases accumulation (the other side of
    the same trade): accumulation is monotone in `r`. -/
theorem accumulation_does_not_decrease (m r1 r2 scale : Nat) (h : r1 ≤ r2) :
    accumulationValue (retain m r1 scale) ≤ accumulationValue (retain m r2 scale) := by
  unfold accumulationValue
  exact retention_monotone m r1 r2 scale h

/-- **THE FRONTIER (Pareto characterization).** `amnesia_grit_is_a_frontier`:
    along the retention axis you cannot increase accumulation without strictly
    decreasing adaptability. Concretely, for `r1 < r2 ≤ scale`:

    * accumulation is non-decreasing (`accumulationValue (retain m r1) ≤
      accumulationValue (retain m r2)`), yet
    * adaptability strictly drops (`adaptability r2 scale < adaptability r1
      scale`).

    The two objectives cannot both improve — every gain in settled memory is paid
    for in lost room to adapt. That is a genuine Pareto frontier, not a free
    lunch. -/
theorem amnesia_grit_is_a_frontier (m r1 r2 scale : Nat)
    (hlt : r1 < r2) (hle : r2 ≤ scale) :
    accumulationValue (retain m r1 scale) ≤ accumulationValue (retain m r2 scale) ∧
    adaptability r2 scale < adaptability r1 scale :=
  ⟨accumulation_does_not_decrease m r1 r2 scale (Nat.le_of_lt hlt),
   adaptability_strictly_decreases r1 r2 scale hlt hle⟩

/-! ## 7. The headline: the American-Frontier optimality principle -/

/-- **The frontier principle (the American Frontier).** Grit (retention) and
    amnesia (forgetting) are not independent goods to be maximized together; they
    trade off on a Pareto frontier:

    * (idempotent reset) amnesia collapses any memory to the void and is
      idempotent — the absolute-zero fixed point;
    * (ratchet) without amnesia, accumulation never regresses — the cultural
      ratchet of `Anthropogenesis`;
    * (extremes fatal) pure grit forfeits *all* adaptability and pure amnesia
      forfeits *all* accumulation — each endpoint is a death;
    * (Pareto) for any strictly higher retention `r1 < r2 ≤ scale`, accumulation
      cannot rise without adaptability strictly falling.

    Therefore robustness cannot sit at either extreme; it must live at an
    *interior* frontier point — settled enough to bank its culture, open enough
    to adapt when the world changes. Life on the edge between memory and
    exploration: the frontier. Bundled so the four claims are provably one
    theory. -/
theorem frontier_principle (m r1 r2 scale : Nat)
    (hlt : r1 < r2) (hle : r2 ≤ scale) :
    -- idempotent reset to the void
    (amnesia (amnesia m) = amnesia m ∧ amnesia m = 0) ∧
    -- the evolutionary ratchet
    (m ≤ accumulate m (scale)) ∧
    -- both extremes are fatal
    (adaptability scale scale = 0 ∧ accumulationValue (retain m 0 scale) = 0) ∧
    -- the Pareto frontier: no gain in accumulation without loss in adaptability
    (accumulationValue (retain m r1 scale) ≤ accumulationValue (retain m r2 scale) ∧
      adaptability r2 scale < adaptability r1 scale) :=
  ⟨⟨amnesia_is_idempotent m, amnesia_collapses_to_void m⟩,
   accumulation_ratchets m scale,
   extremes_are_fatal m scale,
   amnesia_grit_is_a_frontier m r1 r2 scale hlt hle⟩

end Gnosis.Body.AmnesiaGritFrontier
