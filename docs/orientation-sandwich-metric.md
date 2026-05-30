# The Orientation Sandwich and the E8 Prediction Metric

Status: the discrete `FLOOR ≤ structure ≤ CEILING` sandwich is **proved** in
`Gnosis/OrientationSandwichBound.lean` (kernel `decide`/`rfl`, zero axioms;
`#print axioms sandwich_master` reports no dependencies). The quantitative
prediction metric derived below is a **falsifiable conjecture** with stated
tests, **not** a theorem. This document keeps that line sharp: §1 restates what
the Lean module proves; §2–§4 develop the metric and its falsifiers.

---

## 1. What is proved (the discrete sandwich)

The orientation symmetry ladder

```
ORIENTATION  →  SPIN (×2 fibre {-1,+1})  →  2T / 2O / 2I  →  McKay  →  E6 / E7 / E8
```

is pinned below by the universal spin **floor** (the minimal nontrivial binary
cover, index 2) and above by the E8 **ceiling** (maximal exceptional Coxeter
number 30, optimal 8-dimensional kissing number 240). The module proves, by
kernel reduction over already-certified constants, three order facts and bundles
them as `sandwich_master`:

- **Cover-index floor.** Every binary cover in the ladder has index exactly 2
  (`coverIndex .Tetra = coverIndex .Octa = coverIndex .Icosa = 2`), and 2 is the
  minimal nontrivial cover index: `trivialCoverIndex = 1 < 2 = floorIndex`. This
  single 2 equals the spinor fibre length `OrientationSpinorBridge
  .preimageOfOne.length` and the cyclic director-quotient fibre size — one
  universal spin floor.

- **Coxeter sandwich.** `2 < 12 (E6) < 18 (E7) < 30 (E8) = coxeterCeiling`,
  reading the SSOT `DynkinCoxeterClassification.coxeterNumber`. 30 is the strict
  maximum exceptional Coxeter number (it also exceeds h(F4) = 12 and h(G2) = 6),
  and 30 = the 30 edges of the icosahedron = h(E8) (cited numeric coincidence).
  The floor 2 is the spinor / rotation cover level — the `h = 2` belt trick,
  `4π = 2 · 2π`.

- **Kissing / packing ceiling.** Every order-quantity in the ladder (cover
  indices, rotation orders 12/24/60, binary orders 24/48/120, the Coxeter
  ceiling 30) is `≤ 240 = kissingCeiling = E8Lattice.e8Roots.length`, with E8
  achieving 240 exactly. The densest binary order satisfies
  `2 · |2I| = 2 · 120 = 240`: the E8 roots are the 120 positive plus 120
  negative pairs. 240 is the **dimension-8** ceiling (Viazovska 2016, optimal
  8-D kissing number) — above E8 sit the Leech kissing number 196560 and the
  Monster floor 196884, cited only to mark that 240 bounds *dimension 8*, not a
  global maximum.

Read as one chain on the lattice of orientation invariants:

```
floor (spin index 2 / belt-trick h = 2)
   ≤  ladder (E6/E7/E8 Coxeter numbers, all binary covers)
   ≤  ceiling (E8: h = 30, kissing 240)
```

Every `≤` is a kernel-checked decidable order fact; every constant is cited from
an existing certificate (`OrientationSpinorBridge`, `OrientationE8Bridge`,
`OrientationADELadder`, `E8Lattice`, `E8LeechMonsterTower`,
`DynkinCoxeterClassification`). Nothing is re-derived.

What is **not** proved: the SU(2) → SO(3) continuous cover (deferred to Mathlib;
named in `OrientationSpinorBridge`), and every empirical claim in §2–§4 below.

---

## 2. The prediction metric: cross-layer fragment-sharing is bounded by 240

### 2.1 Setup — three projections of one E8 join

The substrate quantizes orientation/state at several "layers", each a finite
geometric sampling of the same orientation manifold:

| Layer | Geometry | Cells | Role |
|-------|----------|-------|------|
| Fano-7 | octonion / `Fano7` lines | 7 points, 7 lines | imaginary-octonion layer |
| d20 / icosahedral | 600-cell shadow, 2I = order 120 | up to 120 director cells | densest SO(3) sampling |
| E8 join | E8 root lattice | 240 roots (kissing) | the optimal 8-D quantizer |

These are not independent codebooks. The octonions sit inside E8 (the E8 lattice
is the integral octavians; the 240 roots are the 240 unit octavians), and the
600-cell / 2I is the icosahedral McKay shadow whose spin cover lands on E8
(`OrientationE8Bridge.icosa_spin_cover_lands_on_E8`). So Fano-7 and the
d20/icosahedral layer are **sub-optimal projections of the E8 join**: each is a
lower-dimensional or lower-order quotient of the same root system.

### 2.2 The fragment-sharing degree

In the distributed-inference cache (`open-source/gnosis/distributed-inference`),
an orientation/state vector is quantized to its nearest lattice cell and that
cell's id keys a reusable **fragment** (a cached partial computation). Define,
for a fixed quantization lattice `L` and a workload `W`:

```
S(L, W)  =  fragment-sharing degree of L on W
         =  (number of distinct fragment-reuse edges induced by L's cells)
            normalized so that S counts, per cell, how many other cells'
            queries legitimately resolve to a shared fragment.
```

Concretely, `S` is the average over occupied cells of the **coordination number**
of that cell under the lattice's reuse relation — how many neighbour cells share
a fragment with it. For a lattice quantizer, the reuse relation is "within one
shell", so the per-cell coordination number is bounded by the lattice's kissing
number (each minimal vector points at one touching neighbour).

### 2.3 The bound and the prediction

**Metric (the explicit formula).** For any layer that is a projection of the E8
join, the cross-layer fragment-sharing degree is bounded by the kissing number
of the densest layer that the projection refines:

```
S(L, W)  ≤  κ(L)                         (per-lattice kissing bound)
S_E8(W)  ≤  κ(E8)  =  240                 (the dimension-8 ceiling)
S_Fano7(W) ≤ κ(Fano7-embed) ≤ 240         (octonion layer ⊂ E8)
S_d20(W)  ≤ κ(2I-shadow) ≤ 240            (icosahedral layer ⊂ E8)
```

with the **join** of the Fano-7 and d20 layers approaching the E8 ceiling from
below as the layers are added:

```
S_Fano7(W)  ≤  S_{Fano7 ∨ d20}(W)  ≤  S_E8(W)  ≤  240,        (monotone fill)
```

and the **fill ratio**

```
ρ(W)  =  S_{join}(W) / 240   ∈ [0, 1]
```

as the single scalar prediction metric. ρ is the measured fraction of the E8
kissing ceiling that the live cache achieves on workload W.

**PREDICTION P1 (ceiling).** Measured cross-layer fragment-sharing never exceeds
240: `S_{join}(W) ≤ 240` for every workload W, i.e. `ρ(W) ≤ 1`. The E8 layer's
coordination number tops out at the kissing number because no point on the
quantization sphere can touch more than 240 others in 8 dimensions (Viazovska
optimality), and the lower layers are projections that cannot exceed their cover.

**PREDICTION P2 (monotone approach).** Adding the icosahedral (d20 / 600-cell)
layer on top of the Fano-7 layer **increases** sharing toward the ceiling:
`S_{Fano7 ∨ d20}(W) ≥ S_Fano7(W)`, with the increase strictly positive on
workloads whose orientation content has icosahedral (order-60/120) structure the
Fano-7 layer alone cannot resolve. The d20 layer fills cells the octonion layer
misses, so ρ rises toward 1.

**PREDICTION P3 (ceiling is dimension-8, not global).** The 240 ceiling is
specific to the 8-D E8 quantizer. A quantizer built on the 24-D Leech layer
would have ceiling 196560, and a Monster-scale layer 196884 (`E8LeechMonsterTower`
constants). So the metric predicts a *regime change*: if the substrate ever
lifts orientation quantization from 8-D (E8) to 24-D (Leech), measured sharing
should be allowed to climb past 240 toward 196560 — and not before.

### 2.4 Falsifiers (stated precisely)

- **P1 falsified** if any instrumented run records a stable cross-layer
  fragment-sharing degree `S_{join}(W) > 240` on an 8-D / E8 quantizer (measured
  over a window large enough that the value is not a transient mis-count). A
  single reproducible `S > 240` on the E8 layer breaks the ceiling claim.

- **P2 falsified** if, on a workload with genuine icosahedral orientation
  content, adding the d20 layer **decreases** or leaves unchanged the measured
  sharing (`S_{Fano7 ∨ d20}(W) < S_Fano7(W)`, beyond measurement noise) — i.e.
  the icosahedral layer is not a fill but a regression.

- **P3 falsified** if an 8-D quantizer is observed sharing past 240 *without*
  lifting to a higher-dimensional lattice, or if lifting to the 24-D layer fails
  to raise the ceiling above 240 when the workload demands it.

Honesty note: P1's *bound* mirrors the proved fact `ladder_below_kissing_ceiling`
(every ladder order-quantity ≤ 240) and the Viazovska optimality theorem, but the
claim that the *measured cache sharing degree* is governed by exactly this
kissing number is an empirical hypothesis about the quantizer's reuse relation,
not a consequence of the Lean module. The Lean module bounds the *group/lattice
orders*; the metric conjectures that the *runtime sharing degree* inherits the
same bound.

---

## 3. Resolution corollary: angular/temporal Nyquist scales with the Coxeter number

The proved Coxeter sandwich `2 < 12 < 18 < 30` gives a second, sharper
prediction about **sampling resolution**.

### 3.1 The corollary

The Coxeter number `h_k` of an exceptional type (E6: 12, E7: 18, E8: 30) is the
order of the Coxeter element — the length of the fundamental rotation cycle that
closes the root system. To resolve level-k orientation structure, the angular (or
temporal) sampling must resolve that cycle, i.e. obey a Nyquist criterion against
`h_k` equally-spaced phases around the cycle.

**Metric (the explicit formula).** To certify orientation symmetry at exceptional
level k, the per-frame director step `Δθ` (the change in the orientation
director between consecutive samples) must satisfy

```
Δθ  <  π / h_k                  (the level-k Nyquist / resolution bound)
```

giving the concrete table

```
level     h_k     required step
E6        12       Δθ < π/12   ≈ 15.0°
E7        18       Δθ < π/18   ≈ 10.0°
E8        30       Δθ < π/30   ≈  6.0°
floor     2        Δθ < π/2    = 90°   (the spin / belt-trick case)
```

The floor `h = 2` is the spinor double cover: `Δθ < π/2` is exactly the
condition that the `4π = 2·2π` belt trick already confirms empirically (you must
sample at least twice per `2π` to see the sheet flip that distinguishes `2π` from
`4π`). The corollary is the upward extension of that single confirmed case to the
exceptional ladder.

Equivalently, in temporal terms with director angular rate `ω` and frame rate
`f`, the requirement is `f > h_k · ω / π`: the frame rate to certify level-k
structure scales **linearly in the Coxeter number** `h_k`.

### 3.2 Predictions and falsifiers

**PREDICTION R1.** A pipeline sampling the orientation director with per-frame
step `Δθ ≥ π/h_k` cannot certify level-k symmetry: the level-k structure aliases.
Specifically, E8 (h = 30) structure requires `Δθ < π/30 ≈ 6°` per frame; coarser
sampling resolves at most the lower level whose Coxeter number it does satisfy.

- **R1 falsifier.** If a run reproducibly certifies level-k orientation symmetry
  (passes the level-k symmetry test) while sampling at `Δθ ≥ π/h_k`, the
  Nyquist-vs-Coxeter scaling is wrong.

**PREDICTION R2 (monotone resolution ladder).** As the per-frame step is reduced
through the thresholds `π/12 → π/18 → π/30`, the highest certifiable level rises
E6 → E7 → E8 in that order and no other — because the proved Coxeter ladder is
strictly `12 < 18 < 30` with nothing between.

- **R2 falsifier.** Observing a certifiable level appear out of order (e.g. E8
  certifiable at a step coarser than the one that first certifies E7), or a
  threshold that does not match `π/h_k` for the SSOT `h_k`.

**PREDICTION R3 (floor already confirmed).** The `h = 2` case `Δθ < π/2` is the
belt trick the experiment confirms; R1/R2 predict the exceptional levels are the
same phenomenon at `h = 12/18/30`. If the floor case held but the exceptional
extension failed at the predicted thresholds, R3 is falsified and the resolution
corollary does not lift off the floor.

Honesty note: the *thresholds* `π/h_k` use the proved Coxeter numbers, but the
claim that "certifying level-k symmetry" in the running renderer/quantizer obeys
exactly this Nyquist relation is an empirical conjecture about the sampling
pipeline, not a theorem. The Lean module proves the Coxeter values and their
strict ordering; it does not prove that the pipeline's resolution behaves as
`π/h_k`.

---

## 4. One-paragraph summary: proved vs predicted

**Proved (the discrete sandwich, zero axioms).**
`Gnosis/OrientationSandwichBound.lean` establishes, by kernel `decide`/`rfl`,
that the orientation/spinor/E8 symmetry ladder is sandwiched
`FLOOR ≤ structure ≤ CEILING`: the universal spin-cover index is exactly 2 and
strictly above the trivial index 1 (the floor); the exceptional Coxeter numbers
ascend strictly `2 < 12 < 18 < 30` with 30 = h(E8) the maximal exceptional
Coxeter number and the 30 icosahedral edges (the Coxeter sandwich); and every
order-quantity in the ladder is `≤ 240`, the E8 root count / optimal 8-D kissing
number, with E8 achieving 240 and `2·|2I| = 240` (the kissing ceiling, with Leech
196560 and Monster 196884 cited above as the higher-dimensional ceilings).
`sandwich_master` bundles all three; `#print axioms sandwich_master` reports no
axiom dependencies. **Predicted (the metric, falsifiable conjectures).** Living
inside that sandwich, the metric predicts that (P1) measured cross-layer cache
fragment-sharing on an 8-D/E8 quantizer never exceeds the kissing ceiling 240,
(P2) adding the icosahedral (d20/600-cell) layer over the Fano-7/octonion layer
increases sharing toward 240, (P3) the 240 ceiling is dimension-8-specific and
lifts to 196560 only on a Leech-scale layer, and that (R1–R3) certifying
orientation symmetry at exceptional level k requires per-frame director step
`Δθ < π/h_k` (`< π/12, π/18, π/30` for E6/E7/E8), the confirmed `h = 2` belt
trick being the floor case. Each prediction carries an explicit falsifier; none
is a theorem — the Lean part bounds the group/lattice orders, the metric
conjectures that the runtime sharing degree and sampling resolution inherit those
same bounds.
