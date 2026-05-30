# The E8 Program

A map of the gnosis-math formalization of E₈ — the lattice, its multiplicative
structure, the roads in and out, and the runtime resolution win it underwrites.
Every entry distinguishes **PROVEN** (machine-checked, axiom footprint stated),
**CITED** (a standard fact stated in a doc, not formalized), and **DEFERRED**
(would need Mathlib). The Init-only project has no Mathlib/Batteries; proofs
close by kernel `decide`/`rfl` (zero-axiom or `propext`-only) except where a
240-element / 240²-pair enumeration forces `native_decide` (which carries
`Lean.ofReduceBool, Lean.trustCompiler`).

Gate per module — `lake build Gnosis.<Module>` — never the full `Gnosis` ledger
(pre-existing RED).

---

## 1. E₈ as an additive lattice

- **`E8Lattice`** — the 240 roots in a scaled integer model (norm²=8), the
  load-bearing `reflection_closure` (closed under the simple reflections ⇒ it
  *is* the E₈ root system), and the Weyl order `696729600 = 240·56·27·16·120` as
  a minuscule coset tower. `native_decide` (the 240-root enumeration).
- **`E8NearestPoint`** — certifies the Conway–Sloane nearest-point **decoder**
  the runtime quantizer uses: parity repair → D₈, glue/coset invariants, E₈
  membership of outputs, round-trip idempotence. **Zero-axiom.** Closes the
  runtime↔proof loop.

## 2. E₈ as a multiplicative (Moufang) loop — and proven the *same* 240

- **`OctavianLoop`** — the 240 unit octavians (integer octonions), `octavian_loop_closure`. `native_decide`.
- **`OctavianMoufangCubic`** — the three degree-3 Moufang identities on the
  octavians, via a certified-fast product `fastOmul`. `native_decide`.
- **`OctavianE8RootBridge`** ✦ — the seam. The irrational "scale by √2" is
  realized as an **explicit 8×8 integer matrix A with AᵀA = 2I** that bijects the
  240 octavians onto the 240 E₈ roots (`mapA_into_e8`/`onto`/`nodup`,
  `g_left_inverse` — **propext-only**) and transports the octonion product onto
  `e8Roots` as a loop `rmul` (closure/identity/inverse — `native_decide`).
- **`MoufangE8Roots`** ✦ — **the 240 E₈ roots are a Moufang loop** under `rmul`.
  All three identities transported via the structural collapse lemma
  `g(rmul r s) = fastOmul (g r)(g s)` — no 240³ brute force. (propext+Quot.sound;
  inherits native_decide from the reused certificates.)

## 3. Orientation → spin → 2I → E₈

- **`OrientationSpinorBridge`** — the discrete 2:1 spin double-cover (squaring
  loses sign; ℤ/4 → ℤ/2; the 4π belt-trick). **Zero / propext.**
- **`OrientationE8Bridge`** — orientation rotation group I (order 60) ×2 spin
  cover → |2I| = 120 = the bottom of the E₈ coset tower = |W(A₄)|;
  `mckayType 2I = E8`. **propext / zero.**
- **`ADEMcKayCorrespondence`** — finite subgroups of SU(2) ↔ affine ADE; 2I↔Ẽ₈,
  |Irr(2I)| = 9 affine nodes, Burnside Σdᵢ²=120. **propext.**

## 4. The cubic Jordan algebra and the magic square

- **`OctavianCubicMagicSquare`** ✦ — the Albert algebra dim **27 = 3 + 3·8**;
  the Freudenthal nesting **78 = 52+(27−1), 133 = 78+(2·27+1), 248 = 133+(2·56+3)**;
  and 27 = |E₆/D₅|, 56 = |E₇/E₆| are coset-tower factors. **propext / zero.**
- **`FreudenthalMagicSquare`** ✦ — the full symmetric 4×4 square over ℝ,ℂ,ℍ,𝕆;
  ten entries `3,8,16,21,35,52,66,78,133,248`, symmetry `M[i][j]=M[j][i]`,
  octonion row = F₄→E₆→E₇→E₈. **propext.**
- **`G2OctonionAutomorphism`** ✦ — dim G₂ = 14 = 2·6+2 (= Der(𝕆)); the exceptional
  ascent 14<52<78<133<248; G₂'s fundamental = the 7 imaginary octonions. **zero / propext.**
- **`DeligneExceptionalSeries`** ✦ — dims `3,8,14,28,52,78,133,248`, dual-Coxeter
  `[2,3,4,6,9,12,18,30]`, h∨=h for ADE but h∨<h for G₂/F₄. **Zero-axiom.**
- **`ExceptionalRepresentations`** ✦ — minimal reps `7,26,27,56,248`; 27=Albert,
  56=fundamentalDim E₇, E₈'s minimal faithful rep = its adjoint = 248. **propext.**
- **`HurwitzDivisionAlgebras`** ✦ — the only normed division algebras have dims
  `1,2,4,8 = 2^k`; Cayley–Dickson doubling; they index the magic square. **zero / propext.**

## 5. Weyl invariant theory

- **`E8ExponentsDegrees`** ✦ — exponents `[1,7,11,13,17,19,23,29]` sum to **120**
  (= #positive roots); invariant degrees `[2,8,12,14,18,20,24,30]` multiply to
  **696729600** (= |W|); degrees = exponents+1; max degree 30 = Coxeter number;
  symmetric pairs all sum to 30. **Zero-axiom.** (Chevalley's |W| = Π deg cited.)

## 6. Lattice / number theory

- **`E8ThetaUnimodular`** ✦ — theta coefficients `r(2n) = 240·σ₃(n)`
  (240, 2160, 6720, 17520, 30240); **det(E₈ Cartan) = 1 proven** (fuel-bounded
  Laplace, kernel `decide`). **propext / zero.** (Θ_E₈ = E₄ deferred.)
- **`LatticeQuantizationGain`** — the runtime quantizer wisdom as theorems: the
  cell-filling predicate, the blend law (8/12 → ~9.3%), the no-zero-pad
  collapse, `deblur_not_cell_filling = false`. **propext / zero.**

## 7. Out to Leech and the Monster

- **`E8LeechMonsterTower`** — `248 = 240 + 8`, `744 = 3·248` (the j-function
  constant = 3·dim E₈), `196884 = 196883 + 1` (McKay's moonshine seed = the
  Hope-Jar `MONSTER_VECTOR_FLOOR`), `24 = 3·8`. **Zero-axiom.**
- **`LeechLatticeArithmetic`** — Leech kissing `196560 = 1104+97152+98304`
  (Conway orbits) `= 240·819`; Steiner octads 759. **Zero-axiom.**
- **`ConwayLeechOrders`** ✦ — `|Co₀| = 2²²·3⁹·5⁴·7²·11·13·23 = 8315553613086720000`,
  `|Co₀| = 2·|Co₁|`. **Zero-axiom.** (Group constructions cited.)

## Concurrent modules (present in the tree this session; authored in parallel, not verified in this map)

`IcosianE8Congruence`, `IcosianE8Equivariance` (icosian ↔ E₈), `SpinCoverSO4F4`,
`SpinCoverTowerToMonster` (spin-cover tower), `TrialitySevenSynthesis` (the SEVEN
and THREE hinges), `CubicPlasticShells` (the plastic/Perrin cubic), `HeptagonCubicShells`
(ℚ(2cos 2π/7) shells), `CoverRingNumberSequences`. See each module's own header
for its proven/cited/deferred claims.

---

## The runtime payoff (distributed-inference, staged)

The same E₈ lattice gives a measured resolution gain in the inference path, all
additive/default-off, decoder Lean-certified (`E8NearestPoint`):

- **`e8_quantizer.rs`** — E₈ normalized second moment G = 0.0716 vs cubic 0.0833 =
  **14.1% lower quantization error** (theory-matched); 240-root neighbor shell.
- **`kv_cache_e8.rs` / `embed_e8.rs`** — **full ~14%** on KV-cache (head_dim 64/128)
  and embeddings (Qwen2.5 hidden 896) — multiples of 8, no tail, cell-filling YES.
- **`bcc_voxel.rs`** — BCC (D₃\*) 3-D analog, ~5.8% / fewer samples.
- **`amplituhedron.rs`** — additive E₈-neighbor τ-sieve admission (proven superset).
- **`n_rgb_lattice_quant.rs`** — +9.30% on the centered n_rgb feature, *predicted*
  by the blend law before measuring.
- **Honest negatives:** `mesh_residual_deblur` E₈ = a wash (origin-hugging scalar
  residual, not cell-filling); raw phyle 8-D points are low-rank → ship `bcc-xyz`,
  not `e8-point`, in monster-studio.

## The seams that meet (why this is one object)

`octavian = E8 root` (√2 integer isometry) · `|2I| = 120 = coset-tower bottom` ·
`27 = Albert = |E₆/D₅|` · `56 = |E₇/E₆| = E₇ minuscule` · `248 = 240+8 = dim E₈ =
2·120+8 = minimal faithful rep` · `744 = 3·248` · `196884 = 196883+1 = Hope-Jar
floor` · `8 = 𝕆 = largest Hurwitz dim, tops the octonion row`. Eight roads into,
through, and out of E₈ — proven to be the same eight angles on one lattice.

## Honesty ledger

The verify-before-prove gate caught these false suggestions **at the kernel**,
none shipped: Leech `2³·3³·…` (was half → `2⁴`); Leech c(3) sum short by c(1);
"G₂ 14 = 7+7 roots" (G₂ has 12 roots); Conway "196560 ∤ |Co₀|" (it divides);
the Deligne dimension *formula* non-integral for G₂/F₄ (dropped, cited). The
kernel is the arbiter; surviving claims are machine-checked.
