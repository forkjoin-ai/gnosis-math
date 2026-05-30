/-
  OctavianE8RootBridge
  ====================

  The octavian ↔ E8-root seam: tying the MULTIPLICATIVE Moufang loop of the 240
  unit octavians (`OctavianLoop`, doubled model, normSq 4) to the ADDITIVE E8
  root lattice (`E8Lattice`, scaled model, normSq 8).

  ──────────────────────────────────────────────────────────────────────────
  THE EXPLICIT √2-ISOMETRY (found by search, certified here)
  ──────────────────────────────────────────────────────────────────────────
  The octavian units have normSq 4; the E8 roots have normSq 8. The textbook
  relation is "scale by √2", which is irrational and cannot be a coordinate map
  over `Int`. The honest question is whether the TWO SPECIFIC integer coordinate
  models used in `OctavianLoop` and `E8Lattice` are related by an *integer*
  √2-isometry. They ARE: there is an explicit 8×8 integer matrix

        ⎡ 1  1  0  0  0  0  0  0 ⎤
        ⎢ 1 −1  0  0  0  0  0  0 ⎥
        ⎢ 0  0  1  0  1  0  0  0 ⎥
    A = ⎢ 0  0  1  0 −1  0  0  0 ⎥          with   Aᵀ A = 2·I.
        ⎢ 0  0  0  1  0  1  0  0 ⎥
        ⎢ 0  0  0  1  0 −1  0  0 ⎥
        ⎢ 0  0  0  0  0  0  1  1 ⎥
        ⎣ 0  0  0  0  0  0  1 −1 ⎦

  `Aᵀ A = 2I` means `A` doubles the squared norm (4 ↦ 8) and is √2 times an
  orthogonal matrix — exactly the √2-isometry, realised in integers. Applying
  `A` to each of the 240 octavians (normSq 4) lands EXACTLY on the 240 E8 roots
  (normSq 8), bijectively and onto.

  The inverse is `g = Aᵀ / 2` (exact `/2` on every E8 root, because `A`'s image
  is precisely the octavian set), and `g (mapA u) = u`.

  ──────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN HERE  (no sorry, no new axiom, no Classical)
  ──────────────────────────────────────────────────────────────────────────
  (a) COORDINATE BIJECTION (the `×√2` isometry, in integers):
      * `mapA_doubles_norm`     — `normSq (mapA v) = 2 · normSq v` for every
                                  octavian (so 4 ↦ 8).
      * `mapA_into_e8`          — every `mapA octavian` is an E8 root.
      * `mapA_images_nodup`     — the 240 images are pairwise distinct.
      * `mapA_onto_e8`          — the image set equals `e8Roots` (bijection onto).
      * `g_left_inverse`        — `g (mapA u) = u` for every octavian (so `mapA`
                                  is injective with explicit two-sided inverse).
      * `AtA_eq_2I`             — the matrix identity `Aᵀ A = 2 I`, the structural
                                  reason `A` is the √2-isometry (decided as a
                                  Gram-matrix fact on the 8 column vectors).

  (b) LOOP-STRUCTURE TRANSPORT onto `e8Roots`:
      * `rmul r s := mapA (omul (g r) (g s))` — the octonion product transported
        along the bijection to a binary operation ON the E8 roots.
      * `rmul_closure`          — `e8Roots` is CLOSED under `rmul` (all 240×240).
      * `e8Identity`            — `mapA octIdentity = (2,2,0,…,0)`, an E8 root.
      * `rmul_has_identity`     — `e8Identity` is a two-sided `rmul`-identity.
      * `rmul_inverse`          — `rinv r := mapA (oconj (g r))` is a two-sided
                                  `rmul`-inverse and is again an E8 root.
      * `octavian_e8_loop_master` — the bundle.

  So the multiplicative Moufang-loop structure of the octavians is carried onto
  the additive E8 root system: `e8Roots` becomes a Moufang loop `(rmul, e8Identity,
  rinv)` isomorphic to the octavian loop via `mapA`. (The Moufang IDENTITIES
  themselves transport automatically because `mapA`/`g` are mutually inverse and
  `OctavianMoufangCubic` proves them on the octavians; we record closure +
  identity + inverses here and state the identity-transport as the next step,
  to keep this module's enumeration cost bounded — see "Next exploration".)

  ──────────────────────────────────────────────────────────────────────────
  PROVEN vs CITED
  ──────────────────────────────────────────────────────────────────────────
  PROVEN (computationally, this module): the explicit integer √2-isometry `A`
  bijects the 240 octavians onto the 240 E8 roots, doubles the norm, has the
  exact integer inverse `g`, and carries the octonion product to a closed loop
  operation `rmul` on `e8Roots` with identity and inverses.

  CITED (the surrounding geometric fact this realises): the octavian integral
  octonion lattice, rescaled by √2, is isometric to the E8 lattice — i.e. the
  unit Moufang loop and the E8 root system are "the same 240 directions". This
  module exhibits the witness `A` and certifies its action on the minimal
  vectors; it does not re-derive the full lattice isometry abstractly.

  ──────────────────────────────────────────────────────────────────────────
  AXIOM FOOTPRINT
  ──────────────────────────────────────────────────────────────────────────
  The light claims that fit in `decide` (Aᵀ A = 2I, the norm-doubling, into-E8,
  onto-E8, nodup, left-inverse, identity facts) are proven by `decide` and are
  PROPEXT-ONLY (no `ofReduceBool`/`trustCompiler`). The heavy 240×240 closure
  (`rmul_closure`, `rmul_inverse`) uses `native_decide` — a brute force over
  57600 products of the transported octonion product is otherwise infeasible —
  pulling `Lean.ofReduceBool` + `Lean.trustCompiler` like the `OctavianLoop`
  closure it transports. Reported per-theorem below. No `sorryAx`.
-/

import Gnosis.OctavianMoufangCubic
import Gnosis.E8Lattice

namespace Gnosis.OctavianE8RootBridge

open Gnosis.OctavianLoop
open Gnosis.OctavianMoufangCubic

-- `decide` over the 240-element octavian / e8 lists needs a deeper
-- kernel recursion budget than the default 512.
set_option maxRecDepth 4000

-- ══════════════════════════════════════════════════════════
-- THE INTEGER √2-ISOMETRY  A  (Aᵀ A = 2 I)
-- ══════════════════════════════════════════════════════════

/-- The √2-isometry `A` applied to a length-8 integer vector, in closed form:
    `A` is the integer matrix with `Aᵀ A = 2 I` (see header) that doubles the
    squared norm. Reads coordinates by `getD`; for a length-8 input the result
    is again length 8. Verified to map the 240 octavians (normSq 4) bijectively
    onto the 240 E8 roots (normSq 8). -/
def mapA (v : List Int) : List Int :=
  let v0 := v.getD 0 0; let v1 := v.getD 1 0; let v2 := v.getD 2 0
  let v3 := v.getD 3 0; let v4 := v.getD 4 0; let v5 := v.getD 5 0
  let v6 := v.getD 6 0; let v7 := v.getD 7 0
  [ v0 + v1,
    v0 - v1,
    v2 + v4,
    v2 - v4,
    v3 + v5,
    v3 - v5,
    v6 + v7,
    v6 - v7 ]

/-- The inverse map `g = Aᵀ / 2`, in closed form. On every E8 root the `/2` is
    exact (because `A`'s image is exactly the octavian set), so `g` maps the 240
    E8 roots back to the 240 octavians and is a genuine two-sided inverse of
    `mapA`. -/
def g (v : List Int) : List Int :=
  let v0 := v.getD 0 0; let v1 := v.getD 1 0; let v2 := v.getD 2 0
  let v3 := v.getD 3 0; let v4 := v.getD 4 0; let v5 := v.getD 5 0
  let v6 := v.getD 6 0; let v7 := v.getD 7 0
  [ (v0 + v1) / 2,
    (v0 - v1) / 2,
    (v2 + v3) / 2,
    (v4 + v5) / 2,
    (v2 - v3) / 2,
    (v4 - v5) / 2,
    (v6 + v7) / 2,
    (v6 - v7) / 2 ]

/-- The eight columns of `A` (as length-8 integer vectors). Used to certify the
    Gram identity `Aᵀ A = 2 I` directly as inner products of columns. -/
def aColumns : List (List Int) :=
  [ [1, 1, 0, 0, 0, 0, 0, 0],
    [1, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 1, -1] ]

/-- **`AtA_gram`** (the `Aᵀ A = 2 I` certificate). For every ordered pair of
    columns `(i,j)`, the inner product equals `2` when `i = j` and `0`
    otherwise — i.e. each column has `normSq = 2` and distinct columns are
    orthogonal. This is the Gram matrix `Aᵀ A = 2 I`, the structural reason `A`
    is the √2-isometry (it doubles every inner product, hence every squared
    norm). PROPEXT-ONLY (`decide`). -/
theorem AtA_gram :
    ((List.range 8).flatMap (fun i => (List.range 8).map (fun j =>
        decide (OctavianLoop.dot (aColumns.getD i []) (aColumns.getD j [])
              = (if i = j then 2 else 0))))).all id = true := by decide

-- ══════════════════════════════════════════════════════════
-- (a)  THE COORDINATE BIJECTION  octavians ↔ e8Roots
-- ══════════════════════════════════════════════════════════

/-- `mapA` doubles the squared norm of every octavian: `normSq (mapA v) = 2 ·
    normSq v`. Since every octavian has `normSq 4`, every image has `normSq 8` —
    the integer realisation of the `×√2` scaling. PROPEXT-ONLY (`decide`). -/
theorem mapA_doubles_norm :
    octavians.all (fun v =>
      OctavianLoop.normSq (mapA v) == 2 * OctavianLoop.normSq v) = true := by
  decide

/-- Consequently every image lands in the normSq-8 shell. PROPEXT-ONLY. -/
theorem mapA_image_norm8 :
    octavians.all (fun v => OctavianLoop.normSq (mapA v) == 8) = true := by
  decide

/-- **`mapA_into_e8`.** Every `mapA octavian` is one of the 240 E8 roots: the
    octavian set maps INTO `E8Lattice.e8Roots` under the explicit integer map
    `mapA`. PROPEXT-ONLY (`decide`). -/
theorem mapA_into_e8 :
    octavians.all (fun v => E8Lattice.e8Roots.contains (mapA v)) = true := by
  decide

/-- The 240 images are pairwise distinct (so `mapA` is injective on the
    octavians). PROPEXT-ONLY (`decide`). -/
theorem mapA_images_nodup :
    (octavians.map mapA).Nodup := by decide

/-- **`mapA_onto_e8`.** Conversely every E8 root is hit: each root equals
    `mapA u` for some octavian `u`. With `mapA_into_e8` + `mapA_images_nodup`
    + the equal counts (240 = 240), `mapA` is a BIJECTION of the octavians onto
    the E8 roots. PROPEXT-ONLY (`decide`). -/
theorem mapA_onto_e8 :
    E8Lattice.e8Roots.all (fun r => (octavians.map mapA).contains r) = true := by
  decide

/-- **`g_left_inverse`.** `g (mapA u) = u` for every octavian `u`: the explicit
    integer matrix `g = Aᵀ/2` is a two-sided inverse of `mapA` on the octavian
    set (the `/2` is exact). This pins `mapA` as a genuine coordinate bijection,
    not merely a count match. PROPEXT-ONLY (`decide`). -/
theorem g_left_inverse :
    octavians.all (fun u => g (mapA u) == u) = true := by decide

/-- `g` sends every E8 root back to an octavian (the bijection's inverse maps
    E8 ⟶ octavians). PROPEXT-ONLY (`decide`). -/
theorem g_into_octavians :
    E8Lattice.e8Roots.all (fun r => octavians.contains (g r)) = true := by
  decide

/-- **Bijection bundle (a).** The explicit integer √2-isometry `mapA` (inverse
    `g`) carries the 240 octavians (normSq 4) bijectively onto the 240 E8 roots
    (normSq 8): norm-doubling, into-E8, distinct images, onto-E8, two-sided
    inverse. PROPEXT-ONLY. -/
theorem octavian_e8_bijection :
    octavians.all (fun v => OctavianLoop.normSq (mapA v) == 8) = true
  ∧ octavians.all (fun v => E8Lattice.e8Roots.contains (mapA v)) = true
  ∧ (octavians.map mapA).Nodup
  ∧ E8Lattice.e8Roots.all (fun r => (octavians.map mapA).contains r) = true
  ∧ octavians.all (fun u => g (mapA u) == u) = true :=
  ⟨mapA_image_norm8, mapA_into_e8, mapA_images_nodup, mapA_onto_e8,
   g_left_inverse⟩

-- ══════════════════════════════════════════════════════════
-- (b)  TRANSPORTED LOOP STRUCTURE  on  e8Roots
-- ══════════════════════════════════════════════════════════

/-- The octonion product transported along the bijection to a binary operation
    ON the E8 roots: `rmul r s = A · ( g(r) · g(s) )`, where the inner product is
    the octavian octonion product `fastOmul` (certified equal to `omul` on
    octavians by `OctavianMoufangCubic.fast_eq_omul`). Uses `fastOmul` so the
    240×240 closure is feasible. -/
def rmul (r s : List Int) : List Int :=
  mapA (fastOmul (g r) (g s))

/-- The transported identity: `mapA octIdentity = (2,2,0,0,0,0,0,0)`, an E8 root
    of `family1`. -/
def e8Identity : List Int := mapA OctavianLoop.octIdentity

/-- The transported inverse: `rinv r = A · conj(g r)`. -/
def rinv (r : List Int) : List Int := mapA (oconj (g r))

/-- The transported identity is the concrete E8 root `(2,2,0,…,0)`. PROPEXT-ONLY. -/
theorem e8Identity_value :
    e8Identity = [2, 2, 0, 0, 0, 0, 0, 0] := by decide

/-- The transported identity is an E8 root. PROPEXT-ONLY (`decide`). -/
theorem e8Identity_is_root :
    E8Lattice.e8Roots.contains e8Identity = true := by decide

/-- **`rmul_closure`.** `e8Roots` is CLOSED under the transported product `rmul`:
    all 240×240 = 57600 products land back in `e8Roots`. This carries
    `OctavianLoop.octavian_loop_closure` along the bijection — the additive E8
    root system inherits the octavians' multiplicative (Moufang-loop) closure.
    Uses `native_decide` (57600 transported octonion products is otherwise
    infeasible). Footprint: `ofReduceBool` + `trustCompiler` + `propext`. -/
theorem rmul_closure :
    (E8Lattice.e8Roots.flatMap (fun r =>
        E8Lattice.e8Roots.map (fun s => rmul r s))).all
      (fun w => E8Lattice.e8Roots.contains w) = true := by native_decide

/-- **`rmul_has_identity`.** `e8Identity = (2,2,0,…,0)` is a two-sided identity
    for `rmul` on `e8Roots`. Carries `OctavianLoop.octavian_loop_has_identity`.
    Uses `native_decide` (240 transported products each way).
    Footprint: `ofReduceBool` + `trustCompiler` + `propext`. -/
theorem rmul_has_identity :
    E8Lattice.e8Roots.all (fun r =>
      rmul e8Identity r == r && rmul r e8Identity == r) = true := by
  native_decide

/-- **`rmul_inverse`.** For every E8 root `r`, `rinv r` is again an E8 root and
    is the two-sided `rmul`-inverse of `r` (`rmul r (rinv r) = rmul (rinv r) r =
    e8Identity`). Carries `OctavianLoop.octavian_loop_inverse`. Uses
    `native_decide`. Footprint: `ofReduceBool` + `trustCompiler` + `propext`. -/
theorem rmul_inverse :
    E8Lattice.e8Roots.all (fun r =>
      E8Lattice.e8Roots.contains (rinv r)
        && (rmul r (rinv r) == e8Identity)
        && (rmul (rinv r) r == e8Identity)) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **OCTAVIAN ↔ E8-ROOT MASTER.** The multiplicative octavian Moufang loop maps
    onto the additive E8 root system via the explicit integer √2-isometry
    `mapA` (`Aᵀ A = 2 I`):

      (1) `mapA_into_e8`     — the 240 octavians map INTO `e8Roots`;
      (2) `mapA_images_nodup`— with 240 distinct images and equal counts (240),
                               this is a BIJECTION octavians → e8Roots;
      (3) `mapA_onto_e8`     — and it is ONTO;
      (4) `g_left_inverse`   — with the explicit integer inverse `g = Aᵀ/2`;
      (5) `rmul_closure`     — the octonion product transports to a CLOSED
                               operation `rmul` on `e8Roots`;
      (6) `rmul_has_identity`— with two-sided identity `e8Identity = (2,2,0,…,0)`;
      (7) `rmul_inverse`     — and two-sided inverses `rinv`.

    So `(e8Roots, rmul, e8Identity, rinv)` is a loop isomorphic (via `mapA`) to
    the octavian loop — the multiplicative Moufang structure carried onto the
    additive E8 lattice's minimal vectors. -/
theorem octavian_e8_loop_master :
    octavians.all (fun v => E8Lattice.e8Roots.contains (mapA v)) = true
  ∧ (octavians.map mapA).Nodup
  ∧ E8Lattice.e8Roots.all (fun r => (octavians.map mapA).contains r) = true
  ∧ octavians.all (fun u => g (mapA u) == u) = true
  ∧ (E8Lattice.e8Roots.flatMap (fun r =>
        E8Lattice.e8Roots.map (fun s => rmul r s))).all
      (fun w => E8Lattice.e8Roots.contains w) = true
  ∧ E8Lattice.e8Roots.all (fun r =>
      rmul e8Identity r == r && rmul r e8Identity == r) = true
  ∧ E8Lattice.e8Roots.all (fun r =>
      E8Lattice.e8Roots.contains (rinv r)
        && (rmul r (rinv r) == e8Identity)
        && (rmul (rinv r) r == e8Identity)) = true :=
  ⟨mapA_into_e8, mapA_images_nodup, mapA_onto_e8, g_left_inverse,
   rmul_closure, rmul_has_identity, rmul_inverse⟩

/-! ## Reading

  `OctavianLoop` certifies the 240 unit octavians are CLOSED under octonion
  MULTIPLICATION (a Moufang loop). `E8Lattice` certifies the 240 E8 roots are
  CLOSED under the Weyl REFLECTIONS (the additive root system). This module
  exhibits the explicit integer √2-isometry `A` (with `Aᵀ A = 2 I`) that bijects
  the octavians (normSq 4) onto the E8 roots (normSq 8), and transports the
  octonion product to a closed loop operation `rmul` on `e8Roots`. The
  multiplicative and additive certificates are thereby tied into one object: the
  same 240 directions, carrying both structures.

  -- Next exploration:
  --   Transport the Moufang IDENTITIES (`OctavianMoufangCubic.octavian_moufang_left/
  --   right/middle`) onto `e8Roots` under `mapA`: prove that `(e8Roots, rmul)`
  --   satisfies the three degree-3 Moufang laws, making it a fully certified
  --   Moufang loop in the E8 coordinates (not merely closed with identity +
  --   inverses). The transport is structural — `mapA`/`g` are mutually inverse,
  --   so each identity pulls back to its octavian form — but a direct
  --   `native_decide` is a 240³ ≈ 13.8M-triple enumeration of nested `rmul`
  --   (each `rmul` is a `g`/`fastOmul`/`mapA` sandwich), so it likely needs the
  --   `fast_eq_omul`-style certified-fast-product trick applied to `rmul`, or a
  --   structural lemma `rmul (rmul …) = mapA (fastOmul (fastOmul …))` to collapse
  --   the sandwich before enumerating. Second seam: prove `rmul` and the E8 Weyl
  --   reflection `E8Lattice.reflect` interact as expected (e.g. left-multiplication
  --   by a root realises a specific reflection composition), welding the
  --   multiplicative loop and the additive reflection group on the one 240-set.
-/

end Gnosis.OctavianE8RootBridge
