import Init

/-!
# KnotEcosystem — Organism State as a 55-Dimensional Pleroma Knot

This module formalizes the contract that the rest of the stack speaks in code:

* Rust kernel  : `wasm-modules/aeon-bioecology/src/knot.rs`
* TS mirror    : `open-source/aeon-3d/src/organism-knot.ts`

Every living organism's state is a point on a fixed-width 55-lane knot vector.
`KNOT_DIM = 55` is the aeon-55d composite / Phyle carrier width — the same
substrate as personality-knot and the Fano-7 / monster196884 knot store, so
organism state, personality, and the FOIL cache all speak one representation.

## What is proven here

1. `knotDim = 55` and its pleroma derivation `(7 - 1) * 9 + 1 = 55`
   (the Heptad-minus-clinamen, ninefold, plus the +1 clinamen residue —
   see `Gnosis.GnosisNumbersAreStructural` for 1/7/9 as structural numbers,
   and `Gnosis.PleromaticMonsterMesh` / `Gnosis.BettiSignatureSieve` for the
   pleroma knot manifold this width carries).

2. `OrganismKnot := Fin 55 → Int` — a fixed 55-component lane vector. The lanes
   are quantized integers (the kernel quantizes f64 lanes to i64 before hashing),
   so the Lean model is exact and decidable.

3. `knotKey : OrganismKnot → KnotKey` — the O(1) identity / FOIL cache key. The
   key reads ONLY the 31 behaviorally-relevant lanes (0..30); the reserved
   headroom lanes (31..54) are excluded by construction.

   Witness theorems (all `0 sorry`, `0 new axiom`):
   * `knotKey_refl` / `knotKey_congr` — identical knots give identical keys
     (key determinism: a knot is a function, equal inputs give equal outputs).
   * `reserved_lanes_independent` — writing any reserved lane (31..54) does NOT
     change the key (headroom must not perturb the cache key).
   * `key_depends_only_on_behavioral_lanes` — two knots that agree on lanes
     0..30 have equal keys regardless of what they hold in lanes 31..54.
   * `key_fixed_width` — the key is a fixed-length (31-element) list, so equality
     / lookup is one fixed-width comparison independent of the 55-D ambient
     space: this is the O(1) identity over a 55-dimensional space.

4. `KnotEcosystem` = a `List OrganismKnot`, and `step` is a pure function of that
   list. `step_deterministic` shows equal ecosystems step to equal results, and
   `step_factors_through_keys` shows the per-organism contribution is a function
   of the knot key alone — which is exactly what justifies the FOIL cache
   teleport (recompute -> key lookup). The ecological dynamics the knot encodes
   (predator/prey, herbivory, mutualism, competition, population update) are the
   semantics of `Gnosis.Ecosystem` in `Gnosis/EcosystemSimulation.lean` and the
   neural overlay in `Gnosis/NeuralEcosystemIntegration.lean`; here we treat that
   per-tick transition abstractly as `tickContribution` so the cache-soundness
   argument is independent of the (heavy) concrete dynamics module.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace KnotEcosystem

/-! ## 1. The pleroma dimension -/

/-- The pleroma / Phyle carrier width. -/
def knotDim : Nat := 55

/-- Reserved-lane base: lanes `31..54` are headroom, excluded from the key. -/
def reservedBase : Nat := 31

/-- Number of behaviorally-relevant lanes (0..30 inclusive). -/
def behavioralLanes : Nat := reservedBase  -- 31

/-- Pleroma derivation: `(Heptad − Clinamen) · 9 + Clinamen = 6·9 + 1 = 55`.
    The 7 (Heptad) and 1 (Clinamen) and 9 are structural gnosis numbers
    (`Gnosis.GnosisNumbersAreStructural`). -/
theorem knotDim_pleroma : (7 - 1) * 9 + 1 = knotDim := by decide

theorem knotDim_eq : knotDim = 55 := rfl

theorem reservedBase_lt_knotDim : reservedBase < knotDim := by decide

/-! ## 2. Canonical lane layout (stable contract for Rust + TS + D1 + dash)

These mirror `knot.rs` / `organism-knot.ts` exactly. -/

def LANE_KINGDOM         : Nat := 0   -- 0..5 kingdom code
def LANE_TROPHIC         : Nat := 1   -- 0..4 trophic role
def LANE_ENERGY          : Nat := 2   -- metabolic reserve
def LANE_POP_WEIGHT      : Nat := 3   -- organisms represented
def LANE_POS_X           : Nat := 4
def LANE_POS_Y           : Nat := 5
def LANE_POS_Z           : Nat := 6
def LANE_CHAR_LEN        : Nat := 7
def LANE_NEURAL_CAP      : Nat := 8
def LANE_LEARNING        : Nat := 9
def LANE_MEMORY          : Nat := 10
def LANE_ENERGY_REQ      : Nat := 11
def LANE_CONNECTIVITY    : Nat := 12
def LANE_GENETIC         : Nat := 13
def LANE_ADAPT           : Nat := 14
def LANE_NICHE           : Nat := 15
def LANE_EVO_AGE         : Nat := 16
def LANE_REPRO           : Nat := 17
def LANE_METABOLIC       : Nat := 18
def LANE_BODY_PLAN       : Nat := 19
def LANE_PHASE_COHERENCE : Nat := 20
def LANE_RESONANCE       : Nat := 21  -- 0 latent / 1 active / 2 extinct
def LANE_SIGNAL_BASE     : Nat := 22  -- 7 one-hot lanes 22..28
def LANE_ADAPTIVE_CAP    : Nat := 29
def LANE_COLLECTIVE_INTEL: Nat := 30
def LANE_RESERVED_BASE   : Nat := 31  -- 31..54 reserved headroom

theorem reservedBase_layout : LANE_RESERVED_BASE = reservedBase := rfl

/-- The signal one-hot block (lanes 22..28) is the 7 neural-signal types
    (Electrical, Chemical, Mycelial, Photosynthetic, Protist, Archaeal,
    Bacterial) — a Heptad, the same 7 that seeds the pleroma derivation. -/
theorem signal_block_is_heptad :
    LANE_ADAPTIVE_CAP - LANE_SIGNAL_BASE = 7 := by decide

/-! ## 3. The knot and its O(1) key -/

/-- A 55D organism knot: a fixed-width lane vector. Lanes are quantized
    integers (the kernel quantizes its `f64` lanes to `i64` before hashing). -/
abbrev OrganismKnot := Fin knotDim → Int

/-- The cache key is the tuple of the 31 behaviorally-relevant lanes (0..30),
    in order. Fixed length, independent of the 55-D ambient space. -/
abbrev KnotKey := List Int

/-- Read a lane by raw index, clamping out-of-range to 0 (mirrors `get`). -/
def laneAt (k : OrganismKnot) (i : Nat) : Int :=
  if h : i < knotDim then k ⟨i, h⟩ else 0

/-- The O(1) identity key: the behavioral lanes 0..30 in order. Reserved lanes
    (31..54) are never read. -/
def knotKey (k : OrganismKnot) : KnotKey :=
  (List.range behavioralLanes).map (fun i => laneAt k i)

/-- The key always has exactly `behavioralLanes` (= 31) entries, regardless of
    the 55-dimensional ambient space. Equality of two keys is therefore a single
    fixed-width comparison: O(1) identity over a 55-D space. -/
theorem key_fixed_width (k : OrganismKnot) : (knotKey k).length = behavioralLanes := by
  unfold knotKey
  rw [List.length_map, List.length_range]

theorem key_width_is_31 (k : OrganismKnot) : (knotKey k).length = 31 := by
  rw [key_fixed_width]; rfl

/-- Key determinism (reflexivity): the key of a knot equals itself. Trivial but
    it is the soundness floor of using the key as a cache lookup. -/
theorem knotKey_refl (k : OrganismKnot) : knotKey k = knotKey k := rfl

/-- Key congruence: identical knots have identical keys. A knot is a function;
    equal functions produce equal keys. -/
theorem knotKey_congr {a b : OrganismKnot} (h : a = b) : knotKey a = knotKey b := by
  rw [h]

/-! ### Reserved-lane independence (the headroom guarantee) -/

/-- Overwrite a single reserved lane `r` (must be ≥ 31) with value `v`. -/
def writeLane (k : OrganismKnot) (r : Fin knotDim) (v : Int) : OrganismKnot :=
  fun i => if i = r then v else k i

/-- The key reads only lanes `< 31`, so writing a reserved lane (`r.val ≥ 31`)
    leaves every read in the key unchanged. -/
theorem reserved_lanes_independent
    (k : OrganismKnot) (r : Fin knotDim) (v : Int) (hr : reservedBase ≤ r.val) :
    knotKey (writeLane k r v) = knotKey k := by
  unfold knotKey
  apply List.map_congr_left
  intro i hi
  have hi' : i < behavioralLanes := by
    simpa [List.mem_range] using hi
  -- the i-th behavioral lane is below 31, hence below r.val, hence ≠ r.val
  have hir : i ≠ r.val := by
    have : i < r.val := Nat.lt_of_lt_of_le hi' hr
    exact Nat.ne_of_lt this
  unfold laneAt writeLane
  by_cases hk : i < knotDim
  · simp only [hk, dif_pos]
    have : (⟨i, hk⟩ : Fin knotDim) ≠ r := by
      intro hcontra
      apply hir
      exact congrArg Fin.val hcontra
    simp [this]
  · simp only [hk, dif_neg, not_false_iff]

/-- General form: any two knots that agree on the behavioral lanes (0..30) have
    equal keys, no matter what they store in the reserved headroom (31..54).
    This is the precise sense in which the 31-lane key is the organism's identity
    over the full 55-D space. -/
theorem key_depends_only_on_behavioral_lanes
    {a b : OrganismKnot}
    (hagree : ∀ i, i < behavioralLanes → laneAt a i = laneAt b i) :
    knotKey a = knotKey b := by
  unfold knotKey
  apply List.map_congr_left
  intro i hi
  have hi' : i < behavioralLanes := by simpa [List.mem_range] using hi
  exact hagree i hi'

/-! ## 4. The knot ecosystem and cache-teleport soundness

A `KnotEcosystem` is a list of organism knots. Its `step` is a pure function of
that list. The per-organism per-tick transition is the ecology dynamics of
`Gnosis.Ecosystem` (`Gnosis/EcosystemSimulation.lean`) — predator/prey,
herbivory, mutualism, competition, population update — and the neural overlay of
`Gnosis/NeuralEcosystemIntegration.lean`. Here we hold that transition abstract
as `tickContribution` so the cache-soundness argument is independent of the
(heavy) concrete dynamics module: the only fact we need is that the contribution
of an organism to one tick is a function of its knot key. -/

abbrev KnotEcosystem := List OrganismKnot

/-- The behaviorally-observable contribution of a single organism to one tick.
    By the contract, it factors through the cache key: it depends only on the
    31 behavioral lanes, never on the reserved headroom. We model that directly
    by defining it over the key. (Any concrete `Gnosis.Ecosystem` transition that
    only reads the behavioral lanes satisfies this; that is the design rule the
    kernel enforces.) -/
def tickContribution (key : KnotKey) : Int := key.foldl (· + ·) 0

/-- One ecosystem tick: each organism contributes through its knot key, then the
    contributions are aggregated (here, summed — standing in for the population /
    energy update of `Gnosis.Ecosystem`). The result is a pure function of the
    knot list. -/
def step (eco : KnotEcosystem) : Int :=
  (eco.map (fun k => tickContribution (knotKey k))).foldl (· + ·) 0

/-- `step` is deterministic: equal ecosystems step to equal results. This is the
    purity that makes a content-addressed (knot-keyed) cache sound. -/
theorem step_deterministic {e₁ e₂ : KnotEcosystem} (h : e₁ = e₂) :
    step e₁ = step e₂ := by rw [h]

/-- The per-organism contribution factors through the knot key: two organisms
    with the same key have the same tick contribution. This is exactly the FOIL
    cache-teleport invariant — a cache hit (key match) can serve the stored
    contribution instead of recomputing the tick. -/
theorem tickContribution_factors_through_key
    {a b : OrganismKnot} (h : knotKey a = knotKey b) :
    tickContribution (knotKey a) = tickContribution (knotKey b) := by
  rw [h]

/-- Cache-teleport soundness for a single organism: if a cached organism `cached`
    shares the live organism's key, substituting it into a tick is sound — the
    contribution is identical, so the teleport (serve cache instead of compute)
    changes nothing observable. -/
theorem cache_teleport_sound
    {live cached : OrganismKnot} (hkey : knotKey live = knotKey cached) :
    tickContribution (knotKey live) = tickContribution (knotKey cached) :=
  tickContribution_factors_through_key hkey

/-- Behavioral indistinguishability for one tick: two organisms that agree on the
    behavioral lanes (0..30) — even if their reserved headroom differs — produce
    the same tick contribution. Reserved-lane writes are observationally inert. -/
theorem behaviorally_indistinguishable_for_one_tick
    {a b : OrganismKnot}
    (hagree : ∀ i, i < behavioralLanes → laneAt a i = laneAt b i) :
    tickContribution (knotKey a) = tickContribution (knotKey b) :=
  tickContribution_factors_through_key (key_depends_only_on_behavioral_lanes hagree)

/-- Whole-ecosystem teleport: if two ecosystems are key-wise equal organism by
    organism, they step identically. The cache can replace any organism with a
    same-key cached one across the whole tick without changing the result. -/
theorem step_factors_through_keys
    {e₁ e₂ : KnotEcosystem}
    (h : e₁.map knotKey = e₂.map knotKey) :
    step e₁ = step e₂ := by
  unfold step
  have hmap : e₁.map (fun k => tickContribution (knotKey k))
            = e₂.map (fun k => tickContribution (knotKey k)) := by
    have h1 : e₁.map (fun k => tickContribution (knotKey k))
            = (e₁.map knotKey).map tickContribution := by
      rw [List.map_map]; rfl
    have h2 : e₂.map (fun k => tickContribution (knotKey k))
            = (e₂.map knotKey).map tickContribution := by
      rw [List.map_map]; rfl
    rw [h1, h2, h]
  rw [hmap]

end KnotEcosystem
end Gnosis
