# The E8 Resolution Program

A synthesis of the E8 work that spans the Lean ledger
(`open-source/gnosis-math/Gnosis/`) and the inference runtime
(`open-source/gnosis/distributed-inference/src/`). The two halves answer
two different questions:

- **Lean half** — *why* E8: the finite, decidable arithmetic that ties
  orientation → spin cover → the binary icosahedral group 2I → McKay →
  the E8 root system → the j-function → the Monster floor.
- **Runtime half** — *what E8 buys*: E8 is the optimal 8-D lattice
  quantizer, and a measured ~14% MSE reduction over the cubic lattice
  shows up end-to-end on a real cell-filling feature.

This document is factual. Every claim below is tagged **PROVEN** (a
machine-checked Lean theorem, with its axiom footprint), **MEASURED** (a
runtime benchmark number, cold vs warm where relevant), **CITED** (a
mathematical fact stated as a constant or motivation, not formalized
here), or **NEGATIVE** (a measured non-result). No "X IS the Y" identity
claims are made; relationships are stated as *equals / decomposes as /
maps to / is the coefficient of*.

A note on the word "resolution": it is overloaded here on purpose. In
the Lean half it is the *resolution of the C²/2I quotient singularity*
whose exceptional fibre has the E8 Dynkin dual graph (geometric
motivation, not formalized). In the runtime half it is *spatial /
numerical resolution* — quantization error per sample. The bridge
between them is the lattice itself.

---

## 1. The chain

```
 ORIENTATION         SPIN 2:1 COVER       2I (SU(2), order 120)      McKAY            E8 ROOT SYSTEM      dim E8            j-FUNCTION             MONSTER
 SO(3) rotation  ──▶  {-1,+1} fibre   ──▶  binary icosahedral   ──▶  2I↔Ẽ8       ──▶  240 roots      ──▶  248 = 240+8  ──▶  744 = 3·248      ──▶  196884 = 196883+1
 group I, order 60    doubles the          = 2·|I| = 2·60                          (Weyl tower             (#roots +         (j constant term)     = Hope-Jar floor
                      rotation group       = E8 Weyl tower bottom                  696729600)              rank/Cartan)
```

Each arrow, with the Lean theorem(s) that close it and the axiom
footprint (verified by `#print axioms`):

| Arrow | Lean theorem(s) | Module | Axiom footprint |
|---|---|---|---|
| orientation → 2:1 spin cover | `squaring_is_double_cover`, `toDirector_two_to_one`, `preimage_is_two` | `OrientationSpinorBridge` (8952a8c) | **none** (`square…`) / `propext` |
| spin cover (×2 = `{-1,+1}` fibre) → 2I | `binary_is_2to1_spin_cover`, `binary_cover_doubles_each`, `shared_cover_index_two` | `OrientationE8Bridge` (dd531c2) | `propext` |
| 2I → E8 (McKay) | `mckay_icosa` (`mckayType .BinaryIcosa = .E8`), `mckay_2I_E8_round_trip`, `mckay_2I_quiver_matches_affine_E8` | `ADEMcKayCorrespondence` (c209216) | `rfl` / `propext` |
| 2I order = E8 Weyl tower bottom | `icosa_order_eq_E8_tower_bottom`, `burnside_2I_eq_weyl_A4`, `icosa_spin_cover_lands_on_E8` | `ADEMcKayCorrespondence` / `OrientationE8Bridge` | **none** / `propext` |
| E8 = 240 roots (closed under Weyl) | `e8_root_count` (=240), `reflection_closure`, `e8_norm_homogeneous` | `E8Lattice` | `Lean.ofReduceBool, Lean.trustCompiler` (`native_decide`) |
| Weyl order self-similar tower | `weyl_e8_tower` (=696729600), `hope_jar_capacity` | `E8Lattice` | `Lean.ofReduceBool, Lean.trustCompiler` |
| 248 = 240 + 8 (dim E8 = #roots + rank) | `e8_dim_decomposes` | `E8LeechMonsterTower` | **none** (`decide`) |
| 744 = 3·248 (j constant term) | `j_constant_eq_three_e8` | `E8LeechMonsterTower` | **none** |
| 196884 = 196883 + 1 (McKay 1978) | `mckay_relation`, `hope_jar_e8_moonshine_tower` | `E8LeechMonsterTower` | **none** |

**Axiom footprint, read precisely.** There are exactly three regimes:

- The McKay seam, the orientation/spin chain, and the E8↔moonshine
  arithmetic close by *kernel* `decide` / `rfl`, so they reach at most
  `propext` (often nothing). These carry **no** compiler-trust
  dependency. Verified, e.g.:
  - `icosa_order_eq_E8_tower_bottom` — *does not depend on any axioms*.
  - `squaring_is_double_cover` — *does not depend on any axioms*.
  - `hope_jar_e8_moonshine_tower` — *does not depend on any axioms*.
  - `orientation_E8_bridge_master`, `mckay_2I_E8_round_trip` — `[propext]`.
- `E8Lattice` itself uses `native_decide` for the 240-root / reflection-
  closure / Weyl-tower facts, so its theorems depend on
  `[Lean.ofReduceBool, Lean.trustCompiler]`. Verified:
  - `E8Lattice.reflection_closure` — `[Lean.ofReduceBool, Lean.trustCompiler]`.
  - `E8Lattice.e8_root_count` — `[Lean.ofReduceBool, Lean.trustCompiler]`.

  This matters: the *root-system certificate itself* trusts the compiled
  evaluator, whereas the seams that connect E8 to 2I and to the Monster
  floor are kernel-checked. The McKay seam was deliberately built with
  `decide`/`rfl` only (the `ADEMcKayCorrespondence` header calls this the
  "higher plane of resolution"), so it does not inherit
  `trustCompiler` even though it imports `E8Lattice`.

**What the chain proves, in one line.** The largest finite rotation
group of orientation (the icosahedral `I`, order 60), doubled by the
spin `{-1,+1}` fibre to 120, equals `|2I|`, which McKay sends to E8 and
which sits at the bottom `[240, 56, 27, 16, 120]` of the E8 Weyl coset
tower (`= |W(A4)| = 5!`); the E8 root count 240 plus the rank 8 gives
`dim E8 = 248`; three copies give the j-invariant constant term
`744 = 3·248`; and the q¹-coefficient `196884 = 196883 + 1` is the
Hope-Jar / `MONSTER_VECTOR_FLOOR` runtime floor.

**Honest scope of the chain.** Everything above is *finite / order-level
/ arithmetic*. The continuous `SU(2) → SO(3)` Lie-group 2:1 cover is
**not** built — `OrientationSpinorBridge` and `OrientationE8Bridge` both
name it as the deferred Mathlib piece. So 2I is not formalized as the
literal SU(2)-preimage of `I < SO(3)`; what is machine-checked is that
the *orders* line up exactly as a 2:1 cover demands and lock onto E8.

---

## 2. The runtime resolution win

E8 is the optimal lattice vector quantizer in dimension 8: its
normalized second moment `G(E8) = 929569/12960000 ≈ 0.071682` is the
lowest of any 8-D lattice, versus the cubic integer lattice ℤ⁸ with
`G(ℤ⁸) = 1/12 ≈ 0.083333`. At equal cell density that is a ~14% lower
mean-squared quantization error per sample — denser, more isotropic
Voronoi cells, with 240 equidistant nearest neighbours (the 240 root
directions).

The runtime carries the Conway–Sloane O(n) nearest-point decoder
(`e8_quantizer.rs`: `nearest_e8`, decoding `D8 ∪ (D8 + ½)` then scaling
to the Lean ×2 integer model) and pins the Lean facts as compile-time
contract constants (`THEOREM_ROOT_COUNT = 240`, `THEOREM_ROOT_NORMSQ =
8`, `THEOREM_REFLECTION_CLOSURE`). It does not re-prove them; its tests
assert the runtime 240-root shell matches the Lean root count and norms.

### Measured numbers (this machine, `cargo test --release`)

All E8/BCC NSM numbers are over N=200000 deterministic SplitMix64 samples;
the n_rgb numbers are on the real image `imaging/noaa_debug.png` (2080×80).

| Quantizer | Measured G (warm) | Cubic baseline | Ratio | Error reduction | Theoretical G |
|---|---|---|---|---|---|
| **E8** (8-D, `e8_quantizer.rs`) | 0.071616 | 0.083353 | 0.8592 | **14.1% lower** | 0.071682 |
| **BCC** (3-D, `bcc_voxel.rs`) | 0.078614 | 0.083437 | 0.9422 | **5.8% lower** | 0.078543 |

E8 cold/warm were identical (deterministic samples); decode cost ~57–66
ns/pt (E8) vs sub-µs for cubic round — E8 is ~15–40× slower to decode but
off the hot path.

**End-to-end win on the `n_rgb` feature (`n_rgb_lattice_quant.rs`).** The
12-D per-channel compass feature, after per-vector DC removal, measures
out as cell-filling on the real image (effective dim 10.60/12,
mean |corr| 0.0469, spread 2.78 cells, verdict CELL-FILLING: YES):

- per-coordinate MSE at step 0.02: E8Tail (one full E8 cell + 4-D cubic
  tail) is **+10.80%** vs cubic ℤ¹²; the E8⊕E8 zero-pad variant is only
  **+0.75%** (see the negative ledger).
- end-to-end over 499200 feature vectors: cubic RMSE 0.005773, E8Tail
  RMSE 0.005498, ratio 0.9524 → **+9.30% MSE reduction vs cubic** —
  matching the predicted blended edge `(8/12)·14% ≈ 9%` (8 of 12 dims
  take the E8 win, the 4-D tail cannot form a cell).

### THE RECIPE (what makes E8 bite, distilled from the measurements)

1. **Center / remove DC.** Subtract the per-vector mean before
   quantizing, add it back after. Raw origin-hugging vectors waste the
   lattice on a constant offset and measure as a wash (the un-centred
   `n_rgb` number was effectively the same as centred here only because
   its DC is small; on the deblur lift the DC dominates — see §3).
2. **One full E8 cell per 8 decorrelated dims + a CUBIC tail.** For
   `d % 8 ≠ 0`, round the `d mod 8` leftover cubically. **Never
   zero-pad** the tail up to a multiple of 8 — the dead pad dims pin each
   block near a lattice point, collapse the effective per-block
   dimension, and re-introduce the wash (the +0.75% E8⊕E8-pad result).
3. **Expect a blended edge `(8·blocks / d) × 14%`.** For `d` a multiple
   of 8 (KV head_dim 64/128) that is the full ~14%; for `d = 12` it is
   ~9%.
4. **Cell-filling precondition, measured FIRST.** The ~14% edge is real
   only when samples spread ~uniformly across a Voronoi cell:
   high-dimensional, decorrelated (low inter-dim |ρ|), at a step matched
   to the feature energy so samples span MULTIPLE cells. Both
   `n_rgb_lattice_quant.rs` and `kv_cache_e8.rs` ship a
   `characterize_cell_filling` diagnostic (effective dim via the
   participation ratio, inter-dim correlation, spread-in-cells) and tie
   the asserted win to its verdict — if not cell-filling, the wash is
   the valid finding.

---

## 3. The honesty ledger

### PROVEN (finite / decidable, machine-checked)

- E8 has exactly 240 roots, every root norm² = 8 in the scaled integer
  model, and the 240 are **closed under the simple reflections** (so they
  are the E8 root system, not 240 arbitrary norm-8 vectors) —
  `E8Lattice.e8_root_count`, `e8_norm_homogeneous`, `reflection_closure`
  (footprint `Lean.ofReduceBool, Lean.trustCompiler`, via `native_decide`).
- The E8 Weyl order 696729600 factors as the self-similar coset tower
  `[240, 56, 27, 16, 120]` — `E8Lattice.weyl_e8_tower`. Hope-Jar capacity
  `30·240·96768 = 696729600` derives from the lattice
  (`hope_jar_capacity`, `capacity_derives_from_lattice`).
- McKay's bijection: the 5 finite SU(2) subgroup families map bijectively
  to {A, D, E6, E7, E8}; `2I` (order 120) maps to E8; Burnside `Σdᵢ² = 120
  = |2I|`; |Irr(2I)| = 9 = #nodes(Ẽ8); marks sum to 30 = h(E8) —
  `ADEMcKayCorrespondence.*` (footprint `propext` / none).
- The orientation → spin → 2I → E8 finite chain at the order level:
  each binary order = 2×rotation order, the 2 being the `{-1,+1}` spinor
  fibre; 60 → 120 = |2I| = tower bottom = |W(A4)|; shared 2:1 index —
  `OrientationSpinorBridge.*`, `OrientationE8Bridge.*` (footprint
  `propext` / none).
- The E8↔moonshine arithmetic: `248 = 240+8`, `744 = 3·248`, `744 =
  24·31`, `196884 = 196883+1`, `196884 = 196560 + 324` (Leech-kissing
  echo), `24 = 3·8` (Leech dimensional ascent), and the runtime
  `hopeJarMonsterFloor = 196884` seam — `E8LeechMonsterTower.*`
  (footprint **none**, kernel `decide`, Init-only).

### MEASURED (runtime benchmarks, cold vs warm)

- E8 NSM 0.071616 vs cubic 0.083353 → **14.1% lower error** (theoretical
  ratio 0.8602; measured 0.8592). Cold = warm (deterministic). Decode
  ~57–66 ns/pt.
- BCC NSM 0.078614 vs cubic 0.083437 → **5.8% lower error** (3-D analog,
  `bcc_voxel.rs`).
- `n_rgb` (real image, cell-filling YES): E8Tail per-coord MSE **+10.80%**,
  end-to-end MSE **+9.30%** vs cubic ℤ¹² (predicted ≈9%). E8 end-to-end
  decode ~29 ms vs ~7.9 ms cubic over 499200 vectors.
- E8 on a synthetic cell-filling residual stream (deblur property test):
  **14.0% lower** MSE than cubic — the geometry works in isolation.

### CITED (mathematical facts, stated as constants / motivation, not formalized)

- `G(E8) = 929569/12960000 ≈ 0.071682` (the optimal 8-D lattice
  constant); `G(BCC) ≈ 0.078543`; both are runtime `const`s, derived from
  the literature, validated against the measured NSM, not proven here.
- The Leech kissing number 196560, the 24 Niemeier lattices, the Monster
  group order, and the j-invariant as a modular function over ℂ — all
  cited as constants in `E8LeechMonsterTower`; only the Nat arithmetic
  around them is proven.
- The C²/2I quotient-singularity resolution whose exceptional fibre has
  the (finite) E8 Dynkin dual graph — geometric motivation in the
  `ADEMcKayCorrespondence` header, not formalized.

### DEFERRED (needs Mathlib or far more than Init)

- The **continuous `SU(2) → SO(3)` 2:1 Lie-group cover** — the genuine
  group statement that 2I is the SU(2)-preimage of `I < SO(3)`. Both
  orientation bridges name this as their "Next exploration": with
  Mathlib, build the central extension `1 → {-1,+1} → 2I → I → 1` so that
  `|2I| = 120` is a *consequence* of the cover, not a tabulated number.
- The **full Leech lattice construction**: its 196560 minimal vectors,
  even unimodularity in rank 24, rootlessness, the `E8³` glue code, and
  the isomorphism to a Niemeier lattice. Only the dimension count
  `24 = 3·8` is proven.
- The **Monster group**: its order, simplicity, and the genuine
  196883-dimensional irreducible representation — and the actual
  monstrous-moonshine theorem (`dim Vₙ = c(n)` for the graded module
  V♮). Only the coefficient arithmetic `196884 = 196883+1` is proven.
- **Denser quantizers** K12 (Coxeter–Todd) and BW16 (Barnes–Wall), which
  would beat E8⊕E8 in 12-/16-D, are *deliberately not used*: neither is
  formalized in `Gnosis.*` nor has a certified decoder in the tree, so
  the runtime sticks to the certified `nearest_e8`.

### NEGATIVE (measured non-results, with mechanism)

- **Deblur residual quantization is a wash** (`mesh_residual_deblur.rs`).
  On the actual deblur output the E8 residual-noise/cubic ratio measured
  **1.0028 (−0.3%, i.e. marginally worse)**; PSNR essentially identical
  (38.06 vs 37.99 dB). *Mechanism:* the residual feature is the scalar
  monster-folded `final_lift` — origin-hugging (O(0.07)) and, grouped
  into arbitrary raster 8-blocks, spatially correlated. Both collapse the
  effective dimension, so the samples hug the cell origin and cubic and
  E8 round almost identically; E8's isotropic-cell edge never
  materializes. The module reports this and **does not assert** a win
  (the win is asserted only on the cell-filling stream test, where it is
  14.0%).
- **Zero-padding 12 → 16 for E8⊕E8 is a near-wash** (+0.75% on `n_rgb`).
  *Mechanism:* the 4 zero-padded dims are dead coordinates that pin each
  block near a lattice point and collapse the effective per-block
  dimension — the same failure mode, re-introduced by the padding. This
  is why the recipe forbids zero-pad and uses a cubic tail instead.

---

## 4. Where E8 bites vs where it doesn't (the cell-filling map)

The single discriminator is **cell-filling**: do the samples spread
roughly uniformly across a high-dimensional, decorrelated Voronoi cell at
a step that spans multiple cells? If yes, E8's ~14% edge appears; if no,
it is a wash. A practical guide for future integration:

**E8 BITES (cell-filling):**

- **KV-cache key/value vectors** — `head_dim` 64/128 (multiples of 8),
  post-projection near-isotropic and decorrelated across dims. The full
  ~14% case. (Scaffolded in `kv_cache_e8.rs`; see caveat below.)
- **Embedding / projection vectors** — high-D, decorrelated; same regime.
- **The `n_rgb` compass feature** — 12-D, effective dim 10.6/12, |ρ|≈0.05;
  measured **+9.30%** end-to-end via the E8Tail recipe.
- **τ-keys / near-key admission** — the amplituhedron E8-neighbour gate
  (`amplituhedron.rs`, `replay_e8_neighbor`, DEFAULT-OFF): on an exact
  cache miss it admits a stored entry whose E8 cell is a single
  root-step neighbour (difference ∈ the 240-root shell, covenant
  `Gnosis.E8Lattice.reflection_closure`). 240 admissible directions
  around each cell. Asserted by tests to be a **strict superset** of the
  exact-hash path — it never drops a candidate the exact path would have
  kept, and additionally serves one-root-step neighbours.

**E8 DOESN'T (origin-hugging / collapsed / padded):**

- **Scalar residuals / monster-folded lifts** — one scalar per sample,
  origin-hugging, spatially correlated → wash (the deblur −0.3%).
- **Origin-hugging vectors generally** — without DC removal the lattice
  is wasted on a constant; center first.
- **Zero-padded blocks** — dead dims collapse the effective dimension
  (the +0.75% E8⊕E8-pad). Use a cubic tail, never zero-pad.
- **Low effective-dimension data** — anything below ~8 effective dims per
  block cannot fill an E8 cell.

**Integration rule of thumb.** Before claiming any E8 win on a new
feature: (1) construct the vector and center it; (2) run the
cell-filling characterization (effective dim, inter-dim correlation,
spread-in-cells); (3) only if the verdict is cell-filling, lay full E8
cells over the decorrelated dims with a cubic tail and expect
`(8·blocks/d)·14%`; (4) measure end-to-end, cold and warm, and report the
wash honestly if the precondition fails.

---

## Source map

**Lean (`open-source/gnosis-math/Gnosis/`):**

- `E8Lattice.lean` — 240 roots, `reflection_closure`, Weyl tower
  696729600, Hope-Jar capacity. (`native_decide` → `trustCompiler`.)
- `ADEMcKayCorrespondence.lean` — SU(2) finite subgroups ↔ ADE; 2I↔E8;
  E8 seam (commit c209216). (`propext`/none.)
- `OrientationSpinorBridge.lean` (8952a8c) — discrete 2:1 spin cover.
- `OrientationE8Bridge.lean` (dd531c2) — orientation→spin→2I→E8 finite
  chain.
- `E8LeechMonsterTower.lean` — `248=240+8`, `744=3·248`, `196884=196883+1
  = Hope-Jar floor`. (Init-only, kernel `decide`, footprint none.)

  *(Note: the originally-anticipated `E8NearestPoint.lean`,
  `LatticeQuantizationGain.lean`, and `LeechLatticeArithmetic.lean` are
  NOT present in the tree as of this writing; the runtime carries the
  nearest-point decoder and the quantization-gain measurement instead.)*

**Runtime (`open-source/gnosis/distributed-inference/src/`):**

- `e8_quantizer.rs` — Conway–Sloane decode, 240-root shell, measured
  G(E8)=0.0716 vs cubic 0.0833 → 14.1% lower error.
- `bcc_voxel.rs` — BCC 3-D analog, 5.8% lower error.
- `amplituhedron.rs` — E8 τ-neighbour admission gate, proven (test-
  asserted) superset of the exact path, DEFAULT-OFF.
- `n_rgb_lattice_quant.rs` — the **+9.30%** end-to-end win on the 12-D
  `n_rgb` feature (E8Tail recipe; predicted by (8/12)·14%).
- `mesh_residual_deblur.rs` — the honest deblur **NEGATIVE** (origin-
  hugging scalar residual is a −0.3% wash).
- `kv_cache_e8.rs` — KV-cache E8 scaffold (center → E8Tail → cubic tail,
  cell-filling diagnostics). **Caveat:** this file is not registered in
  `lib.rs` and contains an invalid Rust identifier (`0xK_V_seed_fix` at
  the bottom), so it does not currently compile; its numbers are
  predictions/recipe, not yet measured here.
