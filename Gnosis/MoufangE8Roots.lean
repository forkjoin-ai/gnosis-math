/-
  MoufangE8Roots
  ==============

  The three Moufang IDENTITIES transported onto the E8 root system.

  `OctavianE8RootBridge` carries the multiplicative octavian Moufang loop onto
  the 240 E8 roots via the explicit integer √2-isometry `mapA` (`Aᵀ A = 2 I`,
  inverse `g = Aᵀ/2`), defining `rmul r s := mapA (fastOmul (g r) (g s))` and
  proving closure + identity + inverses. It explicitly DEFERS the Moufang
  identities, noting that a direct `native_decide` over the nested `rmul` is a
  240³ ≈ 13.8M-triple enumeration (each `rmul` is a `g`/`fastOmul`/`mapA`
  sandwich) — infeasible. This module completes the transport WITHOUT that brute
  force, via a structural COLLAPSE LEMMA.

  ──────────────────────────────────────────────────────────────────────────
  THE COLLAPSE LEMMA  (the crux — pure structure, no 240³)
  ──────────────────────────────────────────────────────────────────────────
  `OctavianMoufangCubic` already proves the three Moufang identities for
  `fastOmul` on the octavians (`octavian_moufang_left/right/middle`). The seam:
  pull each E8 `rmul`-nest back to the SAME `fastOmul`-nest of `g`-images, where
  the octavian identity already lives, then push back through `mapA`.

  The single structural fact that makes this collapse is:

    `g_rmul`  :  r ∈ e8Roots → s ∈ e8Roots →
                g (rmul r s) = fastOmul (g r) (g s)

  Proof: `rmul r s = mapA (fastOmul (g r) (g s))` by definition; `g r`, `g s`
  are octavians (the bijection inverse lands in octavians), so their `fastOmul`
  is again an octavian (octavian loop closure, carried from `omul` via
  `fast_eq_omul`); and `g (mapA u) = u` for every octavian `u`
  (`g_left_inverse`). Hence the `mapA` is undone exactly.

  With `g_rmul` and `rmul_closure` (each inner `rmul` output is an e8Root, so
  the next `g (rmul …)` pulls back validly), a depth-3 `rmul`-nest collapses to
  `mapA` of the corresponding depth-3 `fastOmul`-nest of `g x`, `g y`, `g z`:

    rmul z (rmul x (rmul z y))
      = mapA (fastOmul (g z) (fastOmul (g x) (fastOmul (g z) (g y))))

  (and likewise for every Moufang shape). Both sides of each octavian Moufang
  identity are such `fastOmul`-nests of the same three octavians `g x, g y, g z`;
  `octavian_moufang_*` says they are EQUAL on octavians, so applying `mapA` to
  both gives the corresponding E8 identity. We reuse the octavian identities
  verbatim — NO 240³ `native_decide` over `rmul`.

  ──────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN HERE  (no sorry, no new axiom, no Classical)
  ──────────────────────────────────────────────────────────────────────────
    * `g_rmul`              — the collapse lemma (above).
    * `moufang_left_E8`     — z(x(zy)) = ((zx)z)y on (e8Roots, rmul).
    * `moufang_right_E8`    — x(z(yz)) = ((xz)y)z on (e8Roots, rmul).
    * `moufang_middle_E8`   — (zx)(yz) = (z(xy))z on (e8Roots, rmul).
    * `e8_roots_moufang_loop` — master: closure + identity + inverses (carried
                              from the bridge) AND the three Moufang identities,
                              so `(e8Roots, rmul, e8Identity, rinv)` is a fully
                              certified Moufang loop in E8 coordinates.

  ──────────────────────────────────────────────────────────────────────────
  AXIOM FOOTPRINT
  ──────────────────────────────────────────────────────────────────────────
  The collapse lemma `g_rmul` is structural; its only computational inputs are
  the bridge facts `g_into_octavians`/`g_left_inverse` (PROPEXT-ONLY, `decide`),
  `OctavianLoop.octavian_loop_closure` and `OctavianMoufangCubic.fast_eq_omul`
  (`native_decide` → `ofReduceBool` + `trustCompiler` + `propext`). The three
  E8 identities reuse `octavian_moufang_left/right/middle` (`native_decide`) and
  `rmul_closure` (`native_decide`). So every theorem here pulls
  `Lean.ofReduceBool` + `Lean.trustCompiler` + `propext` THROUGH its reused
  certificates — NOT from any new 240³ enumeration. Reported per-theorem below.
  No `sorryAx`.
-/

import Gnosis.OctavianE8RootBridge

namespace Gnosis.MoufangE8Roots

open Gnosis.OctavianLoop
open Gnosis.OctavianMoufangCubic
open Gnosis.OctavianE8RootBridge

set_option maxRecDepth 4000

-- ══════════════════════════════════════════════════════════
-- POINTWISE EXTRACTIONS  (bulk `.all` certificates → ∀-on-members)
-- ══════════════════════════════════════════════════════════

/-- Pointwise form of `g_into_octavians`: the bijection inverse `g` of any E8
    root is an octavian. Extracted from the bulk `.all` by `List.all_eq_true`
    (pure list reasoning — does NOT recompute the 240-fold). -/
theorem g_mem_octavians {r : List Int} (hr : r ∈ E8Lattice.e8Roots) :
    g r ∈ octavians := by
  have h := (List.all_eq_true.mp g_into_octavians) r hr
  rw [List.contains_iff_mem] at h
  exact h

/-- Pointwise form of `g_left_inverse`: `g (mapA u) = u` for every octavian. -/
theorem g_mapA_id {u : List Int} (hu : u ∈ octavians) : g (mapA u) = u := by
  have h := (List.all_eq_true.mp g_left_inverse) u hu
  exact eq_of_beq h

/-- Pointwise octavian closure under `fastOmul`: the fast product of two
    octavians is again an octavian. Carried from `OctavianLoop.octavian_loop_closure`
    (closure under `omul`) via `OctavianMoufangCubic.fast_eq_omul`
    (`fastOmul = omul` on octavians) — pure list reasoning over the bulk
    certificates, NOT a fresh enumeration. -/
theorem fastOmul_mem_octavians {u v : List Int}
    (hu : u ∈ octavians) (hv : v ∈ octavians) : fastOmul u v ∈ octavians := by
  -- `fastOmul u v = omul u v` on these octavians …
  have heq : fastOmul u v = omul u v := by
    have hb := (List.all_eq_true.mp ((List.all_eq_true.mp fast_eq_omul) u hu)) v hv
    exact of_decide_eq_true hb
  -- … and `omul u v ∈ octavians` by loop closure.
  have hclo :
      (octavians.flatMap (fun a => octavians.map (fun b => omul a b))).all
        (fun w => octavians.contains w) = true := octavian_loop_closure
  have hmem : omul u v ∈ octavians := by
    have hin : omul u v ∈
        (octavians.flatMap (fun a => octavians.map (fun b => omul a b))) := by
      rw [List.mem_flatMap]
      exact ⟨u, hu, by rw [List.mem_map]; exact ⟨v, hv, rfl⟩⟩
    have hc := (List.all_eq_true.mp hclo) (omul u v) hin
    rw [List.contains_iff_mem] at hc
    exact hc
  rw [heq]; exact hmem

/-- Pointwise form of `rmul_closure`: the transported product of two E8 roots is
    again an E8 root. Extracted from the bulk `.all`. -/
theorem rmul_mem_e8 {r s : List Int}
    (hr : r ∈ E8Lattice.e8Roots) (hs : s ∈ E8Lattice.e8Roots) :
    rmul r s ∈ E8Lattice.e8Roots := by
  have hin : rmul r s ∈
      (E8Lattice.e8Roots.flatMap (fun a =>
        E8Lattice.e8Roots.map (fun b => rmul a b))) := by
    rw [List.mem_flatMap]
    exact ⟨r, hr, by rw [List.mem_map]; exact ⟨s, hs, rfl⟩⟩
  have hc := (List.all_eq_true.mp rmul_closure) (rmul r s) hin
  rw [List.contains_iff_mem] at hc
  exact hc

-- ══════════════════════════════════════════════════════════
-- THE COLLAPSE LEMMA
-- ══════════════════════════════════════════════════════════

/-- **`g_rmul`** (the collapse lemma). For E8 roots `r, s`, the inverse map `g`
    pulls the transported product back to the `fastOmul` of the inverses:

        g (rmul r s) = fastOmul (g r) (g s).

    Proof: `rmul r s = mapA (fastOmul (g r) (g s))` by definition; `g r`, `g s`
    are octavians, so `fastOmul (g r) (g s)` is an octavian (`fastOmul_mem_octavians`),
    and `g (mapA u) = u` for octavians (`g_mapA_id`). This is the structural seam
    that collapses a nested `rmul` to a nested `fastOmul` WITHOUT enumerating the
    240³ triples. -/
theorem g_rmul {r s : List Int}
    (hr : r ∈ E8Lattice.e8Roots) (hs : s ∈ E8Lattice.e8Roots) :
    g (rmul r s) = fastOmul (g r) (g s) := by
  have hoct : fastOmul (g r) (g s) ∈ octavians :=
    fastOmul_mem_octavians (g_mem_octavians hr) (g_mem_octavians hs)
  -- `rmul r s = mapA (fastOmul (g r) (g s))` is definitional.
  show g (mapA (fastOmul (g r) (g s))) = fastOmul (g r) (g s)
  exact g_mapA_id hoct

-- ══════════════════════════════════════════════════════════
-- MOUFANG IDENTITY — LEFT   z(x(zy)) = ((zx)z)y
-- ══════════════════════════════════════════════════════════

/-- **`moufang_left_E8`.** The LEFT Moufang identity holds on `(e8Roots, rmul)`:
    for all E8 roots `x, y, z`,

        rmul z (rmul x (rmul z y)) = rmul (rmul (rmul z x) z) y.

    Both sides collapse (via `g_rmul`, routed through `rmul_closure` so every
    inner product is a valid E8 root) to `mapA` of the corresponding `fastOmul`
    nest of `g x, g y, g z`; those `fastOmul` nests are EQUAL by the octavian
    identity `OctavianMoufangCubic.octavian_moufang_left`. NO 240³ enumeration —
    the octavian identity is reused verbatim. -/
theorem moufang_left_E8
    {x y z : List Int}
    (hx : x ∈ E8Lattice.e8Roots) (hy : y ∈ E8Lattice.e8Roots)
    (hz : z ∈ E8Lattice.e8Roots) :
    rmul z (rmul x (rmul z y)) = rmul (rmul (rmul z x) z) y := by
  -- the three g-images are octavians
  have gx := g_mem_octavians hx
  have gy := g_mem_octavians hy
  have gz := g_mem_octavians hz
  -- LHS: collapse the nest to mapA (fastOmul (g z) (fastOmul (g x) (fastOmul (g z) (g y))))
  have hzy : rmul z y ∈ E8Lattice.e8Roots := rmul_mem_e8 hz hy
  have hxzy : rmul x (rmul z y) ∈ E8Lattice.e8Roots := rmul_mem_e8 hx hzy
  have lhs :
      rmul z (rmul x (rmul z y))
        = mapA (fastOmul (g z) (fastOmul (g x) (fastOmul (g z) (g y)))) := by
    show mapA (fastOmul (g z) (g (rmul x (rmul z y)))) = _
    rw [g_rmul hx hzy, g_rmul hz hy]
  -- RHS: collapse to mapA (fastOmul (fastOmul (fastOmul (g z) (g x)) (g z)) (g y))
  have hzx : rmul z x ∈ E8Lattice.e8Roots := rmul_mem_e8 hz hx
  have hzxz : rmul (rmul z x) z ∈ E8Lattice.e8Roots := rmul_mem_e8 hzx hz
  have rhs :
      rmul (rmul (rmul z x) z) y
        = mapA (fastOmul (fastOmul (fastOmul (g z) (g x)) (g z)) (g y)) := by
    show mapA (fastOmul (g (rmul (rmul z x) z)) (g y)) = _
    rw [g_rmul hzx hz, g_rmul hz hx]
  -- the two fastOmul nests are equal by the octavian Moufang-left identity
  have hoct :
      fastOmul (g z) (fastOmul (g x) (fastOmul (g z) (g y)))
        = fastOmul (fastOmul (fastOmul (g z) (g x)) (g z)) (g y) := by
    have h := (List.all_eq_true.mp
      ((List.all_eq_true.mp
        ((List.all_eq_true.mp octavian_moufang_left) (g x) gx)) (g y) gy)) (g z) gz
    exact of_decide_eq_true h
  rw [lhs, rhs, hoct]

-- ══════════════════════════════════════════════════════════
-- MOUFANG IDENTITY — RIGHT   x(z(yz)) = ((xz)y)z
-- ══════════════════════════════════════════════════════════

/-- **`moufang_right_E8`.** The RIGHT Moufang identity holds on `(e8Roots, rmul)`:

        rmul x (rmul z (rmul y z)) = rmul (rmul (rmul x z) y) z,

    by the same collapse, reusing `OctavianMoufangCubic.octavian_moufang_right`. -/
theorem moufang_right_E8
    {x y z : List Int}
    (hx : x ∈ E8Lattice.e8Roots) (hy : y ∈ E8Lattice.e8Roots)
    (hz : z ∈ E8Lattice.e8Roots) :
    rmul x (rmul z (rmul y z)) = rmul (rmul (rmul x z) y) z := by
  have gx := g_mem_octavians hx
  have gy := g_mem_octavians hy
  have gz := g_mem_octavians hz
  have hyz : rmul y z ∈ E8Lattice.e8Roots := rmul_mem_e8 hy hz
  have hzyz : rmul z (rmul y z) ∈ E8Lattice.e8Roots := rmul_mem_e8 hz hyz
  have lhs :
      rmul x (rmul z (rmul y z))
        = mapA (fastOmul (g x) (fastOmul (g z) (fastOmul (g y) (g z)))) := by
    show mapA (fastOmul (g x) (g (rmul z (rmul y z)))) = _
    rw [g_rmul hz hyz, g_rmul hy hz]
  have hxz : rmul x z ∈ E8Lattice.e8Roots := rmul_mem_e8 hx hz
  have hxzy : rmul (rmul x z) y ∈ E8Lattice.e8Roots := rmul_mem_e8 hxz hy
  have rhs :
      rmul (rmul (rmul x z) y) z
        = mapA (fastOmul (fastOmul (fastOmul (g x) (g z)) (g y)) (g z)) := by
    show mapA (fastOmul (g (rmul (rmul x z) y)) (g z)) = _
    rw [g_rmul hxz hy, g_rmul hx hz]
  have hoct :
      fastOmul (g x) (fastOmul (g z) (fastOmul (g y) (g z)))
        = fastOmul (fastOmul (fastOmul (g x) (g z)) (g y)) (g z) := by
    have h := (List.all_eq_true.mp
      ((List.all_eq_true.mp
        ((List.all_eq_true.mp octavian_moufang_right) (g x) gx)) (g y) gy)) (g z) gz
    exact of_decide_eq_true h
  rw [lhs, rhs, hoct]

-- ══════════════════════════════════════════════════════════
-- MOUFANG IDENTITY — MIDDLE   (zx)(yz) = (z(xy))z
-- ══════════════════════════════════════════════════════════

/-- **`moufang_middle_E8`.** The MIDDLE Moufang identity holds on `(e8Roots, rmul)`:

        rmul (rmul z x) (rmul y z) = rmul (rmul z (rmul x y)) z,

    by the same collapse, reusing `OctavianMoufangCubic.octavian_moufang_middle`. -/
theorem moufang_middle_E8
    {x y z : List Int}
    (hx : x ∈ E8Lattice.e8Roots) (hy : y ∈ E8Lattice.e8Roots)
    (hz : z ∈ E8Lattice.e8Roots) :
    rmul (rmul z x) (rmul y z) = rmul (rmul z (rmul x y)) z := by
  have gx := g_mem_octavians hx
  have gy := g_mem_octavians hy
  have gz := g_mem_octavians hz
  have hzx : rmul z x ∈ E8Lattice.e8Roots := rmul_mem_e8 hz hx
  have hyz : rmul y z ∈ E8Lattice.e8Roots := rmul_mem_e8 hy hz
  have lhs :
      rmul (rmul z x) (rmul y z)
        = mapA (fastOmul (fastOmul (g z) (g x)) (fastOmul (g y) (g z))) := by
    show mapA (fastOmul (g (rmul z x)) (g (rmul y z))) = _
    rw [g_rmul hz hx, g_rmul hy hz]
  have hxy : rmul x y ∈ E8Lattice.e8Roots := rmul_mem_e8 hx hy
  have hzxy : rmul z (rmul x y) ∈ E8Lattice.e8Roots := rmul_mem_e8 hz hxy
  have rhs :
      rmul (rmul z (rmul x y)) z
        = mapA (fastOmul (fastOmul (g z) (fastOmul (g x) (g y))) (g z)) := by
    show mapA (fastOmul (g (rmul z (rmul x y))) (g z)) = _
    rw [g_rmul hz hxy, g_rmul hx hy]
  have hoct :
      fastOmul (fastOmul (g z) (g x)) (fastOmul (g y) (g z))
        = fastOmul (fastOmul (g z) (fastOmul (g x) (g y))) (g z) := by
    have h := (List.all_eq_true.mp
      ((List.all_eq_true.mp
        ((List.all_eq_true.mp octavian_moufang_middle) (g x) gx)) (g y) gy)) (g z) gz
    exact of_decide_eq_true h
  rw [lhs, rhs, hoct]

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **E8-ROOT MOUFANG LOOP MASTER.** `(e8Roots, rmul, e8Identity, rinv)` is a
    fully certified Moufang loop in the E8 coordinates:

      (1) closure       — `rmul_closure` (carried from the octavian loop);
      (2) identity      — `rmul_has_identity` (`e8Identity = (2,2,0,…,0)`);
      (3) inverses      — `rmul_inverse` (`rinv`);
      (4) Moufang-left  — `moufang_left_E8`;
      (5) Moufang-right — `moufang_right_E8`;
      (6) Moufang-middle— `moufang_middle_E8`.

    The Moufang IDENTITIES (4–6) are transported from the octavian loop by the
    structural collapse lemma `g_rmul` — reusing `OctavianMoufangCubic`'s
    octavian identities verbatim, with NO 240³ `native_decide` over `rmul`. This
    completes the `OctavianE8RootBridge` deferred next-step: the multiplicative
    Moufang structure of the 240 unit octavians is carried, identities and all,
    onto the additive E8 root system's 240 minimal vectors. -/
theorem e8_roots_moufang_loop :
    -- closure / identity / inverses (carried by the bridge)
    ((E8Lattice.e8Roots.flatMap (fun r =>
        E8Lattice.e8Roots.map (fun s => rmul r s))).all
      (fun w => E8Lattice.e8Roots.contains w) = true)
  ∧ (E8Lattice.e8Roots.all (fun r =>
      rmul e8Identity r == r && rmul r e8Identity == r) = true)
  ∧ (E8Lattice.e8Roots.all (fun r =>
      E8Lattice.e8Roots.contains (rinv r)
        && (rmul r (rinv r) == e8Identity)
        && (rmul (rinv r) r == e8Identity)) = true)
    -- the three Moufang identities (transported via the collapse lemma)
  ∧ (∀ {x y z : List Int}, x ∈ E8Lattice.e8Roots → y ∈ E8Lattice.e8Roots →
        z ∈ E8Lattice.e8Roots →
        rmul z (rmul x (rmul z y)) = rmul (rmul (rmul z x) z) y)
  ∧ (∀ {x y z : List Int}, x ∈ E8Lattice.e8Roots → y ∈ E8Lattice.e8Roots →
        z ∈ E8Lattice.e8Roots →
        rmul x (rmul z (rmul y z)) = rmul (rmul (rmul x z) y) z)
  ∧ (∀ {x y z : List Int}, x ∈ E8Lattice.e8Roots → y ∈ E8Lattice.e8Roots →
        z ∈ E8Lattice.e8Roots →
        rmul (rmul z x) (rmul y z) = rmul (rmul z (rmul x y)) z) :=
  ⟨rmul_closure, rmul_has_identity, rmul_inverse,
   @moufang_left_E8, @moufang_right_E8, @moufang_middle_E8⟩

/-! ## Reading

  `OctavianE8RootBridge` carried closure + identity + inverses of the octavian
  Moufang loop onto `e8Roots` but DEFERRED the Moufang identities, naming a
  structural collapse lemma as the way past the infeasible 240³ `rmul`
  enumeration. This module supplies that lemma (`g_rmul`) and completes the
  transport: `g (rmul r s) = fastOmul (g r) (g s)` for E8 roots, so each nested
  `rmul` collapses to `mapA` of the matching nested `fastOmul` of the `g`-images,
  where `OctavianMoufangCubic`'s octavian identities already hold. The three E8
  identities therefore reuse the octavian identities verbatim — no new heavy
  enumeration.

  -- Next exploration:
  --   With `(e8Roots, rmul, e8Identity, rinv)` now a fully certified Moufang
  --   loop in E8 coordinates, weld it to the ADDITIVE reflection group: prove the
  --   second seam named in `OctavianE8RootBridge` — that left-multiplication by an
  --   E8 root `rmul r ·` realises a specific composition of E8 Weyl reflections
  --   `E8Lattice.reflect`, tying the multiplicative Moufang loop and the additive
  --   Weyl group on the one 240-set. The collapse lemma `g_rmul` should let that
  --   too be argued structurally (pull `reflect` back through `g`/`mapA`) rather
  --   than by a fresh 240² enumeration.
-/

end Gnosis.MoufangE8Roots
