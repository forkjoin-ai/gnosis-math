/-
  IcosianE8Equivariance.lean
  ==========================

  THE 2I-EQUIVARIANCE OF THE ICOSIAN → E_8 EMBEDDING — the deepest form of the
  icosian/E_8 convergence: not merely the same 240-point set (the prior modules'
  norm/shell/disjoint-union results), but the same GROUP ACTION.  This module
  closes the §8 `Next exploration` (B) of `Gnosis.IcosianE8LatticeIso`: it ties
  `SpinorCover600Cell`'s 2I group (`hom_bridge`, the universal conjugation
  homomorphism) to `IcosianE8LatticeIso`'s golden lattice shell, by showing the
  σ₊⊕σ₋ embedding INTERTWINES the icosian left-multiplication action with an 8×8
  ℤ[φ]-matrix action on the embedded coordinates.

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN  (decidably / by reflection, kernel only, no reals)
  ────────────────────────────────────────────────────────────────────────────

  (1) ORBIT TRANSITIVITY — `icosa` is a SINGLE 2I-orbit (the clean core).
      Starting from `qOne` and left-multiplying by the two generators
      `gens2 = [gi, gg]` (the unit `i` and the golden icosian generator), an
      explicit breadth-first SPANNING TREE (`buildNodes`, folded from a 120-entry
      `(generator, parent)` parent table) reaches all 120 elements: every node is
      `qmulS gens2[gi] (an earlier node)` so all 120 lie in the orbit of `qOne`,
      and `buildNodes` equals `Cover.icosa` as a set (`build_eq_icosa_fwd/bwd`,
      `build_card`).  Therefore the inner E_8 shell `innerShell = embed '' icosa`
      is one orbit of the induced action (`innerShell_is_orbit_image`).

  (2) EMBED INTERTWINES THE ACTION — universal polynomial identity, per generator.
      For each generator `g`, `embed (qmulZ g q) = Mg g (embed q)` for EVERY
      ℤ[φ]-quaternion `q`, where `Mg g` is the 8×8 ℤ[φ]-matrix induced on the
      embedded coordinates by left-multiplication-by-`g` composed with σ₊⊕σ₋ (it is
      BLOCK-DIAGONAL: `L(σ₊ g) ⊕ L(σ₋ g)`, since the two real embeddings are ring
      homomorphisms that do not mix).  This is proved as a POLYNOMIAL IDENTITY in
      `q`'s eight Int-components by the `ZPhi` reflection engine
      (`denote_eq_of_reify_eq`), once per generator (`intertwine_gi`,
      `intertwine_gg`) — NOT by enumerating the 120.  `embed` additivity
      (`embed_add`) and the action's matrix form are recorded alongside.

  (3) CONSEQUENCE — the inner shell is the M-orbit of `embed qOne`, and the
      φ-dilation commutes with `Mg` (`phiScale_comm_Mg`): the golden central scalar
      commutes with the induced matrix action, so the two-shell decomposition
      `innerShell ⊎ φ·innerShell` of `IcosianE8LatticeIso` is the 2I-EQUIVARIANT
      orbit structure of the golden 240.  `equivariance_master` bundles the three.

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS NAMED, NOT FAKED
  ────────────────────────────────────────────────────────────────────────────
  The matrix `Mg g` is ORTHOGONAL (it is the σ₊⊕σ₋ image of a unit-quaternion
  left-multiplication, which is an isometry); we do not re-derive its orthogonality
  here from the norm (the norm-8 preservation already lives in
  `IcosianE8Embedding.embed_norm_eight`, and `Mg`-invariance of the norm follows
  from intertwining + that theorem on the orbit).  The full claim that `Mg`
  generates a Weyl-subgroup action on the integer `E8Lattice.e8Roots` list inherits
  the same irrational O(8) alignment obligation named in `IcosianE8LatticeIso`'s
  `Next exploration` (A) — we work in the golden ℤ[φ]⁸ model where the action is
  exact, and we say so rather than fake the integer-basis identification.

  RELATIONSHIP (precise, never "X IS Y").  `embed` MAPS the 2I left-multiplication
  action to the `Mg`-matrix action: `embed ∘ (qmulZ g ·) = (Mg g) ∘ embed`.  This
  UPGRADES the convergence from a set/shell match to an EQUIVARIANT map of group
  actions, on the golden model.  It does not assert an isomorphism with the
  integer-basis E_8 Weyl action (the named irrational-alignment obligation).

  HARD CONSTRAINTS (met).  Init-only (`import Init` + the cited Gnosis modules).
  Kernel `decide` / `rfl` / structural + the `ZPhi` reflection engine ONLY — NO
  `native_decide`, no `sorry`, no `admit`, no new `axiom`, no `Classical.choice`,
  no `omega`.  `set_option maxRecDepth 8000` (the spanning-tree fold and the
  reflective normalizer recurse deep).  Gate ONLY on
  `lake build Gnosis.IcosianE8Equivariance`.  Does NOT register in `Gnosis.lean`
  and does NOT edit any other module.  `#print axioms` for the headline theorems is
  at the bottom.
-/

import Init
import Gnosis.IcosianE8LatticeIso

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Gnosis
namespace IcosianE8Equivariance

open GR ZPhi Cover IntInst
open Gnosis.IcosianE8Embedding
open Gnosis.IcosianE8LatticeIso

-- ══════════════════════════════════════════════════════════
-- §1  ORBIT TRANSITIVITY — `icosa` is a single 2I-orbit of `qOne`
-- ══════════════════════════════════════════════════════════

/-! We exhibit a breadth-first SPANNING TREE of the left-multiplication action
    rooted at `qOne`.  `parents` is a 120-entry table: entry `i` records
    `(generator-index, parent-index)` so that node `i` is
    `qmulS gens2[generator-index] (node parent-index)`.  Folding the table from
    the seed `[qOne]` builds all 120 nodes (`buildNodes`); BY CONSTRUCTION every
    node is a left-generator-product applied to an earlier node, hence lies in the
    orbit of `qOne`.  We then verify (kernel `decide`) that `buildNodes` is exactly
    `Cover.icosa` as a set — so the orbit of `qOne` is all 120 icosians: a single
    orbit.  This is the orbit-BFS closure pattern that proved `icosa_card`, run
    forward from the identity. -/

/-- Breadth-first spanning-tree parent table for the left-multiplication action of
    `gens2` rooted at `qOne`: entry `i = (gi, pi)` means node `i+1` is
    `qmulS gens2[gi] (node pi)`.  (Computed by the orbit BFS; the explicit table
    makes the closure a cheap linear fold rather than a kernel-heavy nested
    fixpoint.) -/
def parents : List (Nat × Nat) :=
[(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4),
 (1, 5), (0, 6), (1, 6), (1, 7), (0, 8), (1, 8), (1, 9), (0, 10), (1, 10), (0, 11),
 (1, 11), (1, 12), (0, 13), (1, 13), (0, 14), (1, 14), (1, 15), (0, 16), (1, 16), (0, 17),
 (1, 17), (1, 18), (0, 19), (1, 19), (1, 20), (0, 21), (1, 21), (0, 22), (1, 22), (1, 23),
 (0, 24), (1, 25), (0, 26), (1, 26), (0, 27), (1, 27), (1, 28), (0, 29), (1, 29), (1, 30),
 (0, 31), (1, 31), (0, 32), (1, 33), (0, 34), (0, 35), (1, 35), (1, 36), (0, 37), (1, 37),
 (1, 38), (1, 39), (0, 40), (1, 40), (1, 41), (0, 42), (1, 42), (1, 43), (1, 44), (1, 45),
 (0, 46), (1, 46), (0, 47), (1, 48), (0, 49), (0, 50), (1, 50), (0, 52), (1, 52), (1, 53),
 (0, 54), (1, 54), (1, 55), (0, 57), (0, 60), (0, 61), (0, 62), (0, 65), (1, 66), (0, 67),
 (1, 67), (0, 68), (0, 69), (0, 70), (1, 70), (1, 72), (1, 73), (0, 74), (1, 75), (0, 77),
 (0, 79), (0, 80), (0, 83), (1, 85), (1, 89), (1, 91), (1, 92), (1, 93), (0, 95), (0, 96),
 (0, 97), (0, 99), (1, 101), (0, 104), (0, 105), (0, 106), (0, 107), (0, 108), (1, 110)]

/-- The 120 orbit nodes, built from the seed `[qOne]` by the spanning tree: each new
    node is `qmulS gens2[gi] (an earlier node)`.  Every entry is therefore a left
    product of generators applied to `qOne` — a genuine orbit element. -/
def buildNodes : List QZ :=
  parents.foldl (fun acc pr =>
    let g := gens2.getD pr.1 qOne
    let par := acc.getD pr.2 qOne
    acc ++ [qmulS g par]) [qOne]

/-- **(1a)** The spanning tree reaches exactly 120 distinct orbit nodes. -/
theorem build_card : buildNodes.length = 120 := by decide

/-- **(1b)** Every orbit node is one of the 120 icosians (the orbit of `qOne` is
    CONTAINED in `Cover.icosa` — `icosa` is left-generator-invariant). -/
theorem build_sub_icosa : buildNodes.all (fun a => icosa.contains a) = true := by decide

/-- **(1c)** Every icosian is reached by the orbit of `qOne` (`Cover.icosa` is
    CONTAINED in the orbit) — the surjectivity direction that makes it a SINGLE
    orbit. -/
theorem icosa_sub_build : icosa.all (fun a => buildNodes.contains a) = true := by decide

/-- **(1) SINGLE 2I-ORBIT.**  `Cover.icosa` is exactly the orbit of `qOne` under
    left-multiplication by the generators `gens2`: the spanning tree from `qOne`
    reaches 120 nodes, and `buildNodes` and `icosa` contain each other.  The 120
    unit icosians (the 600-cell vertices, the binary icosahedral group 2I) form a
    SINGLE orbit of the identity. -/
theorem icosa_single_orbit :
    buildNodes.length = 120
    ∧ buildNodes.all (fun a => icosa.contains a) = true
    ∧ icosa.all (fun a => buildNodes.contains a) = true := by
  exact ⟨build_card, build_sub_icosa, icosa_sub_build⟩

-- ══════════════════════════════════════════════════════════
-- §2  EMBED INTERTWINES — the induced 8×8 ℤ[φ]-matrix action `Mg`
-- ══════════════════════════════════════════════════════════

/-! Left-multiplication by a fixed `g` on the 4 quaternion ℤ[φ]-coordinates is
    ℤ[φ]-linear: `(qmulZ g q).coords = L(g) · q.coords` with the 4×4 Hamilton
    left-multiplication matrix `L(g)`.  Because σ₊ and σ₋ are RING HOMOMORPHISMS
    ℤ[φ] → ℤ[φ] (the two real embeddings of ℚ(√5), realized inside ℤ[φ]), the
    embedding's σ₊-coordinates of the product depend only on the σ₊-coordinates of
    `q` (through `L(σ₊ g)`), and likewise for σ₋.  Hence the induced 8×8 matrix is
    BLOCK-DIAGONAL: `Mg g = L(σ₊ g) ⊕ L(σ₋ g)`. -/

/-- The 4×4 Hamilton left-multiplication, ℤ[φ]-linear in the second factor's
    coordinates `(vw,vx,vy,vz)`, with coefficients from `g = (gw,gx,gy,gz)`. -/
def Lapply (gw gx gy gz : Zphi) (vw vx vy vz : Zphi) : (Zphi × Zphi × Zphi × Zphi) :=
  ( zsubZ (zsubZ (zsubZ (zmul gw vw) (zmul gx vx)) (zmul gy vy)) (zmul gz vz)
  , zadd (zadd (zmul gw vx) (zmul gx vw)) (zsubZ (zmul gy vz) (zmul gz vy))
  , zadd (zsubZ (zmul gw vy) (zmul gx vz)) (zadd (zmul gy vw) (zmul gz vx))
  , zadd (zsubZ (zadd (zmul gw vz) (zmul gx vy)) (zmul gy vx)) (zmul gz vw) )

/-- **THE INDUCED 8×8 ℤ[φ]-MATRIX ACTION.**  Left-multiplication by `g` on the
    embedded coordinates: block-diagonal `L(σ₊ g) ⊕ L(σ₋ g)`, acting on the
    σ₊-block `(c0,c2,c4,c6)` and the σ₋-block `(c1,c3,c5,c7)` of an `E8Z` point. -/
def Mg (g : QZ) (p : E8Z) : E8Z :=
  let gpw := sigmaPlus  g.w; let gpx := sigmaPlus  g.x
  let gpy := sigmaPlus  g.y; let gpz := sigmaPlus  g.z
  let gmw := sigmaMinus g.w; let gmx := sigmaMinus g.x
  let gmy := sigmaMinus g.y; let gmz := sigmaMinus g.z
  let (pw, px, py, pz) := Lapply gpw gpx gpy gpz p.c0 p.c2 p.c4 p.c6
  let (mw, mx, my, mz) := Lapply gmw gmx gmy gmz p.c1 p.c3 p.c5 p.c7
  { c0 := pw, c1 := mw, c2 := px, c3 := mx, c4 := py, c5 := my, c6 := pz, c7 := mz }

-- ── §2a  Symbolic ℤ[φ]-over-Int reflection scaffolding ─────────────────────────
-- We prove the universal intertwining `embed (qmulZ g q) = Mg g (embed q)` (for ALL
-- `q`, `g` fixed) as a polynomial identity in `q`'s eight Int-components, using the
-- `ZPhi.SZ` symbolic-ℤ[φ]-over-Int machinery and `GR.denote_eq_of_reify_eq`.

/-- symbolic ℤ[φ] subtraction. -/
def szsub (p q : SZ) : SZ := ⟨.sub p.a q.a, .sub p.b q.b⟩
/-- symbolic ℤ[φ] constant from a concrete `Zphi`. -/
def szconstE (c : Zphi) : SZ := ⟨.cst c.a, .cst c.b⟩
/-- symbolic σ₋ (Galois conjugate), `⟨a,b⟩ ↦ ⟨a+b, -b⟩`. -/
def sSigmaMinus (s : SZ) : SZ := ⟨.add s.a s.b, .sub (.cst 0) s.b⟩

theorem szsub_D (env) (p q : SZ) : szD env (szsub p q) = zsubZ (szD env p) (szD env q) := by
  simp only [szD, szsub, zsubZ, zadd, zneg, denote, Ki, Int.sub_eq_add_neg]
theorem szconstE_D (env) (c : Zphi) : szD env (szconstE c) = c := by
  cases c; simp only [szD, szconstE, denote]
theorem sSigmaMinus_D (env) (s : SZ) : szD env (sSigmaMinus s) = sigmaMinus (szD env s) := by
  simp only [szD, sSigmaMinus, sigmaMinus, denote, Ki]
  apply zext
  · show denote Ki env s.a + denote Ki env s.b = denote Ki env s.a + denote Ki env s.b; rfl
  · show (0:Int) + -(denote Ki env s.b) = -(denote Ki env s.b); rw [Int.zero_add]

/-- symbolic q coordinates (eight Int variables, two per ℤ[φ] coordinate). -/
def sqW : SZ := ⟨.var 0, .var 1⟩
def sqX : SZ := ⟨.var 2, .var 3⟩
def sqY : SZ := ⟨.var 4, .var 5⟩
def sqZ : SZ := ⟨.var 6, .var 7⟩

/-- environment binding the eight Int variables to `q`'s coordinate components. -/
def envQ (q : QZ) : Nat → Int :=
  fun i => [q.w.a, q.w.b, q.x.a, q.x.b, q.y.a, q.y.b, q.z.a, q.z.b].getD i 0

theorem sqW_D (q) : szD (envQ q) sqW = q.w := by cases q; simp [szD, sqW, denote, envQ, List.getD]
theorem sqX_D (q) : szD (envQ q) sqX = q.x := by cases q; simp [szD, sqX, denote, envQ, List.getD]
theorem sqY_D (q) : szD (envQ q) sqY = q.y := by cases q; simp [szD, sqY, denote, envQ, List.getD]
theorem sqZ_D (q) : szD (envQ q) sqZ = q.z := by cases q; simp [szD, sqZ, denote, envQ, List.getD]

/-- symbolic Hamilton product `qmulZ g q` with `g` a tuple of constant SZ and `q`
    the four symbolic SZ coordinates — the same Hamilton form as `qmulZ`. -/
def sQmul (g0 g1 g2 g3 : SZ) (q0 q1 q2 q3 : SZ) : (SZ × SZ × SZ × SZ) :=
  ( szsub (szsub (szsub (szmul g0 q0) (szmul g1 q1)) (szmul g2 q2)) (szmul g3 q3)
  , szadd (szadd (szmul g0 q1) (szmul g1 q0)) (szsub (szmul g2 q3) (szmul g3 q2))
  , szadd (szsub (szmul g0 q2) (szmul g1 q3)) (szadd (szmul g2 q0) (szmul g3 q1))
  , szadd (szsub (szadd (szmul g0 q3) (szmul g1 q2)) (szmul g2 q1)) (szmul g3 q0) )

/-- The σ₊⊕σ₋ embedding of the symbolic product, as eight symbolic SZ coordinates
    (σ₊ = identity on SZ, σ₋ = `sSigmaMinus`). -/
def sEmbedProd (g : QZ) : (SZ × SZ × SZ × SZ × SZ × SZ × SZ × SZ) :=
  let p := sQmul (szconstE g.w) (szconstE g.x) (szconstE g.y) (szconstE g.z) sqW sqX sqY sqZ
  (p.1, sSigmaMinus p.1, p.2.1, sSigmaMinus p.2.1, p.2.2.1, sSigmaMinus p.2.2.1,
   p.2.2.2, sSigmaMinus p.2.2.2)

/-- The `Mg`-action on the embedded symbolic `q`, as eight symbolic SZ coordinates:
    `L(σ₊ g)` on the σ₊-block (`sqW,sqX,sqY,sqZ`) and `L(σ₋ g)` on the σ₋-block
    (`sSigmaMinus` of each). -/
def sMgEmbed (g : QZ) : (SZ × SZ × SZ × SZ × SZ × SZ × SZ × SZ) :=
  let lp := sLapply (szconstE g.w) (szconstE g.x) (szconstE g.y) (szconstE g.z)
              sqW sqX sqY sqZ
  let lm := sLapply (sSigmaMinus (szconstE g.w)) (sSigmaMinus (szconstE g.x))
              (sSigmaMinus (szconstE g.y)) (sSigmaMinus (szconstE g.z))
              (sSigmaMinus sqW) (sSigmaMinus sqX) (sSigmaMinus sqY) (sSigmaMinus sqZ)
  (lp.1, lm.1, lp.2.1, lm.2.1, lp.2.2.1, lm.2.2.1, lp.2.2.2, lm.2.2.2)
where
  /-- symbolic 4×4 Hamilton left-multiplication (mirrors `Lapply`). -/
  sLapply (gw gx gy gz vw vx vy vz : SZ) : (SZ × SZ × SZ × SZ) :=
    ( szsub (szsub (szsub (szmul gw vw) (szmul gx vx)) (szmul gy vy)) (szmul gz vz)
    , szadd (szadd (szmul gw vx) (szmul gx vw)) (szsub (szmul gy vz) (szmul gz vy))
    , szadd (szsub (szmul gw vy) (szmul gx vz)) (szadd (szmul gy vw) (szmul gz vx))
    , szadd (szsub (szadd (szmul gw vz) (szmul gx vy)) (szmul gy vx)) (szmul gz vw) )

/-- **THE INTERTWINING, GENERIC IN `q`.**  Given the eight reflected SZ-coordinate
    equalities `reify Ki (sEmbedProd g).i = reify Ki (sMgEmbed g).i` (the `.a` and
    `.b` Int-polynomial normal forms agree), the concrete intertwining
    `embed (qmulZ g q) = Mg g (embed q)` holds for EVERY `q`.  This is the
    reflection-engine reduction: the per-generator `decide`s discharge the eight
    SZ identities, and this bridge lifts them to the concrete map.  (Proof:
    `denote_eq_of_reify_eq` on each coordinate's `.a`/`.b`, evaluated at `envQ q`,
    then a structural unfolding of `embed`/`Mg`/`qmulZ`.) -/
theorem intertwine_of (g : QZ)
    (h0a : reify Ki (sEmbedProd g).1.a       = reify Ki (sMgEmbed g).1.a)
    (h0b : reify Ki (sEmbedProd g).1.b       = reify Ki (sMgEmbed g).1.b)
    (h1a : reify Ki (sEmbedProd g).2.1.a     = reify Ki (sMgEmbed g).2.1.a)
    (h1b : reify Ki (sEmbedProd g).2.1.b     = reify Ki (sMgEmbed g).2.1.b)
    (h2a : reify Ki (sEmbedProd g).2.2.1.a   = reify Ki (sMgEmbed g).2.2.1.a)
    (h2b : reify Ki (sEmbedProd g).2.2.1.b   = reify Ki (sMgEmbed g).2.2.1.b)
    (h3a : reify Ki (sEmbedProd g).2.2.2.1.a = reify Ki (sMgEmbed g).2.2.2.1.a)
    (h3b : reify Ki (sEmbedProd g).2.2.2.1.b = reify Ki (sMgEmbed g).2.2.2.1.b)
    (h4a : reify Ki (sEmbedProd g).2.2.2.2.1.a   = reify Ki (sMgEmbed g).2.2.2.2.1.a)
    (h4b : reify Ki (sEmbedProd g).2.2.2.2.1.b   = reify Ki (sMgEmbed g).2.2.2.2.1.b)
    (h5a : reify Ki (sEmbedProd g).2.2.2.2.2.1.a = reify Ki (sMgEmbed g).2.2.2.2.2.1.a)
    (h5b : reify Ki (sEmbedProd g).2.2.2.2.2.1.b = reify Ki (sMgEmbed g).2.2.2.2.2.1.b)
    (h6a : reify Ki (sEmbedProd g).2.2.2.2.2.2.1.a = reify Ki (sMgEmbed g).2.2.2.2.2.2.1.a)
    (h6b : reify Ki (sEmbedProd g).2.2.2.2.2.2.1.b = reify Ki (sMgEmbed g).2.2.2.2.2.2.1.b)
    (h7a : reify Ki (sEmbedProd g).2.2.2.2.2.2.2.a = reify Ki (sMgEmbed g).2.2.2.2.2.2.2.a)
    (h7b : reify Ki (sEmbedProd g).2.2.2.2.2.2.2.b = reify Ki (sMgEmbed g).2.2.2.2.2.2.2.b)
    (q : QZ) :
    embed (qmulZ g q) = Mg g (embed q) := by
  -- lift each reflected coordinate equality to a concrete `Zphi` equality (via szEq)
  have E0 := szEq (sEmbedProd g).1 (sMgEmbed g).1 h0a h0b (envQ q)
  have E1 := szEq (sEmbedProd g).2.1 (sMgEmbed g).2.1 h1a h1b (envQ q)
  have E2 := szEq (sEmbedProd g).2.2.1 (sMgEmbed g).2.2.1 h2a h2b (envQ q)
  have E3 := szEq (sEmbedProd g).2.2.2.1 (sMgEmbed g).2.2.2.1 h3a h3b (envQ q)
  have E4 := szEq (sEmbedProd g).2.2.2.2.1 (sMgEmbed g).2.2.2.2.1 h4a h4b (envQ q)
  have E5 := szEq (sEmbedProd g).2.2.2.2.2.1 (sMgEmbed g).2.2.2.2.2.1 h5a h5b (envQ q)
  have E6 := szEq (sEmbedProd g).2.2.2.2.2.2.1 (sMgEmbed g).2.2.2.2.2.2.1 h6a h6b (envQ q)
  have E7 := szEq (sEmbedProd g).2.2.2.2.2.2.2 (sMgEmbed g).2.2.2.2.2.2.2 h7a h7b (envQ q)
  -- unfold both sides' `szD` to concrete functions; `embed`/`Mg`/`qmulZ` literally
  simp only [sEmbedProd, sMgEmbed, sMgEmbed.sLapply, szsub_D, szadd_D, szmul_D,
             sSigmaMinus_D, szconstE_D, sqW_D, sqX_D, sqY_D, sqZ_D] at E0 E1 E2 E3 E4 E5 E6 E7
  cases q with
  | mk qw qx qy qz =>
    show E8Z.mk _ _ _ _ _ _ _ _ = E8Z.mk _ _ _ _ _ _ _ _
    simp only [embed, Mg, Lapply, qmulZ, qmulZ.zsub, sigmaPlus, zsubZ] at *
    refine congrArg₈ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact E0
    · exact E1
    · exact E2
    · exact E3
    · exact E4
    · exact E5
    · exact E6
    · exact E7
where
  congrArg₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Zphi}
      (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
      (h₄ : a₄ = b₄) (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
      E8Z.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ = E8Z.mk b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
    subst h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇; rfl

/-- **(2-gi) INTERTWINING, generator `gi` (unit `i`).**  For EVERY ℤ[φ]-quaternion
    `q`, `embed (qmulZ gi q) = Mg gi (embed q)`: the unit-`i` left-multiplication
    intertwines with its induced 8×8 ℤ[φ]-matrix.  The eight SZ identities are
    discharged by kernel `decide` (polynomial identities, not a 120-enumeration). -/
theorem intertwine_gi (q : QZ) : embed (qmulZ gi q) = Mg gi (embed q) :=
  intertwine_of gi
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) q

/-- **(2-gg) INTERTWINING, generator `gg` (golden icosian).**  For EVERY
    ℤ[φ]-quaternion `q`, `embed (qmulZ gg q) = Mg gg (embed q)`: the golden-icosian
    left-multiplication intertwines with its induced 8×8 ℤ[φ]-matrix. -/
theorem intertwine_gg (q : QZ) : embed (qmulZ gg q) = Mg gg (embed q) :=
  intertwine_of gg
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) q

/-- **(2) EMBED ADDITIVITY.**  The embedding is additive on coordinates:
    `embed (qaddZ p q) = (coordinate-wise sum) (embed p) (embed q)` — σ₊, σ₋ are
    additive.  (Recorded as the linear-structure half of the intertwining; the
    `Mg`-matrices are ℤ[φ]-linear, and additivity is what makes the block matrix a
    genuine linear action.) -/
def qaddZ (p q : QZ) : QZ := ⟨zadd p.w q.w, zadd p.x q.x, zadd p.y q.y, zadd p.z q.z⟩
def addE8Z (p q : E8Z) : E8Z :=
  ⟨zadd p.c0 q.c0, zadd p.c1 q.c1, zadd p.c2 q.c2, zadd p.c3 q.c3,
   zadd p.c4 q.c4, zadd p.c5 q.c5, zadd p.c6 q.c6, zadd p.c7 q.c7⟩

theorem embed_add (p q : QZ) : embed (qaddZ p q) = addE8Z (embed p) (embed q) := by
  cases p with
  | mk pw px py pz =>
  cases q with
  | mk qw qx qy qz =>
    cases pw; cases px; cases py; cases pz; cases qw; cases qx; cases qy; cases qz
    show E8Z.mk _ _ _ _ _ _ _ _ = E8Z.mk _ _ _ _ _ _ _ _
    simp only [embed, qaddZ, addE8Z, sigmaPlus, sigmaMinus, zadd]
    refine congrArg₈ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (apply ZPhi.zext <;> simp only [Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.neg_add])
where
  congrArg₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Zphi}
      (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
      (h₄ : a₄ = b₄) (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
      E8Z.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ = E8Z.mk b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
    subst h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇; rfl

-- ══════════════════════════════════════════════════════════
-- §3  CONSEQUENCE — orbit-equals-shell, and φ commutes with `Mg`
-- ══════════════════════════════════════════════════════════

/-! THE SCALE SUBTLETY (stated precisely, not hidden).  `Cover.icosa` stores each
    unit icosian SCALED BY 2, so the GROUP product on the shell is the HALVED
    Hamilton product `qmulS` (= `qmulRaw` then `/2`), not the raw `qmulZ`.  The raw
    intertwining `embed (qmulZ g q) = Mg g (embed q)` (§2) is the UNSCALED linear
    identity: `Mg g` carries the ×2 model to a ×4 result.  The SHELL-PRESERVING
    action is therefore `Ag g := halfE8 ∘ Mg g` — it is `Mg` followed by the
    coordinate halving that returns to the ×2 shell.  This `Ag` (and ONLY `Ag`)
    keeps `innerShell` and `phiShell` set-invariant; the raw `Mg` does not.  We
    record both: the universal linear `Mg`-intertwining (§2) and the shell action
    `Ag` (here). -/

/-- Coordinate-wise halving (the `zhalf` of `SpinorCover600Cell`), the inverse of
    the ×2 scaling.  `Ag` applies it after `Mg` to return to the ×2 shell. -/
def halfE8 (p : E8Z) : E8Z :=
  ⟨zhalf p.c0, zhalf p.c1, zhalf p.c2, zhalf p.c3,
   zhalf p.c4, zhalf p.c5, zhalf p.c6, zhalf p.c7⟩

/-- **THE SHELL-PRESERVING 2I ACTION.**  `Ag g = halfE8 ∘ Mg g`: the induced 8×8
    ℤ[φ]-matrix action rescaled to the ×2 shell, the genuine group action of `g` on
    the embedded 600-cell. -/
def Ag (g : QZ) (p : E8Z) : E8Z := halfE8 (Mg g p)

/-- **(3a-gi) SCALED INTERTWINING, `gi`.**  On the embedded icosians, the SHELL
    group product intertwines with `Ag`: `embed (qmulS gi q) = Ag gi (embed q)` for
    every icosian `q` (the ×2 shell-preserving form of `intertwine_gi`). -/
theorem intertwine_shell_gi :
    icosa.all (fun q => decide (embed (qmulS gi q) = Ag gi (embed q))) = true := by decide
/-- **(3a-gg) SCALED INTERTWINING, `gg`.** -/
theorem intertwine_shell_gg :
    icosa.all (fun q => decide (embed (qmulS gg q) = Ag gg (embed q))) = true := by decide

-- A `List.contains` membership is preserved by mapping any function `f` over the
-- list (no recomputation of the witness; pure list reasoning).
theorem contains_map {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (l : List α) (a : α) (h : l.contains a = true) :
    (l.map f).contains (f a) = true := by
  rw [List.contains_iff_mem] at h ⊢
  exact List.mem_map.2 ⟨a, h, rfl⟩

-- `all (fun a => P.contains a)` over a mapped list, reduced via `contains_map`.
theorem mapped_subset {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (src dst : List α) (P : List β)
    (hsub : src.all (fun a => dst.contains a) = true)
    (hmap : (dst.map f).all (fun b => P.contains b) = true) :
    (src.map f).all (fun b => P.contains b) = true := by
  rw [List.all_eq_true] at *
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hac : dst.contains a = true := by
    have := hsub a ha; simpa using this
  exact hmap (f a) (by
    rw [List.mem_map]
    have : (dst.map f).contains (f a) = true := contains_map f dst a hac
    simpa [List.contains_iff_mem] using this)

-- Every element of a list `List.contains`-belongs to that list — proven generically
-- by structural induction, so instantiating it does NOT force the concrete list's
-- `BEq` comparisons to evaluate (avoids the heavy fold recomputation in a `decide`).
theorem all_self_contains {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.all (fun b => l.contains b) = true := by
  rw [List.all_eq_true]
  intro b hb
  rw [List.contains_iff_mem]
  exact hb

/-- **(3b) INNER SHELL = ORBIT IMAGE.**  The inner E_8 shell `innerShell`
    (= `embed '' icosa`) is the `embed`-image of the single 2I-orbit `buildNodes`:
    the two map-images coincide as sets.  With the scaled intertwining, this
    exhibits `innerShell` as one orbit of `embed qOne` under the shell action `Ag`.
    (Proved from `icosa_single_orbit` by `embed`-image of the mutual `List.contains`
    inclusions and the generic `all_self_contains` — no recomputation of the
    120-node fold inside a fresh `decide`.) -/
theorem innerShell_is_orbit_image :
    (buildNodes.map embed).all (fun p => innerShell.contains p) = true
    ∧ innerShell.all (fun p => (buildNodes.map embed).contains p) = true := by
  refine ⟨?_, ?_⟩
  · -- buildNodes ⊆ icosa, and (icosa.map embed) = innerShell self-contained
    have hinner : (icosa.map embed).all (fun b => innerShell.contains b) = true :=
      all_self_contains innerShell
    exact mapped_subset embed buildNodes icosa innerShell build_sub_icosa hinner
  · -- icosa ⊆ buildNodes, and (buildNodes.map embed) self-contained
    show (icosa.map embed).all (fun p => (buildNodes.map embed).contains p) = true
    exact mapped_subset embed icosa buildNodes (buildNodes.map embed)
      icosa_sub_build (all_self_contains (buildNodes.map embed))

/-- **(3c) INNER SHELL IS `Ag`-INVARIANT.**  Both generators' shell actions map the
    inner 600-cell into itself: `innerShell` is closed under `Ag gi` and `Ag gg` —
    the inner shell is a single (closed) 2I-orbit under the shell action. -/
theorem innerShell_Ag_closed_gi :
    innerShell.all (fun p => innerShell.contains (Ag gi p)) = true := by decide
theorem innerShell_Ag_closed_gg :
    innerShell.all (fun p => innerShell.contains (Ag gg p)) = true := by decide

/-- **(3d) φ COMMUTES WITH THE ACTION (universal).**  The golden central dilation
    `φ·` commutes with the induced matrix action `Mg g` on EVERY `E8Z` point:
    `phiScaleE8Z (Mg g p) = Mg g (phiScaleE8Z p)`.  (φ = ⟨0,1⟩ is a central scalar
    in ℤ[φ]; `Mg` is ℤ[φ]-linear, and `zmul ⟨0,1⟩ ·` commutes through every entry of
    `Lapply` by `zmul_comm`/`zmul_left_comm`.)  Proven for all `p` (not a 120-scan),
    so it holds on both shells. -/
theorem phiScale_comm_Mg (g : QZ) (p : E8Z) :
    phiScaleE8Z (Mg g p) = Mg g (phiScaleE8Z p) := by
  cases p
  simp only [phiScaleE8Z, Mg, Lapply, zphiScale, sigmaPlus, sigmaMinus, zsubZ]
  refine congrArg₈ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [zmul_add, zadd_mul, zneg_mul, ← zmul_assoc,
               zmul_comm ⟨(0:Int),(1:Int)⟩, zmul_left_comm ⟨(0:Int),(1:Int)⟩]
where
  congrArg₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Zphi}
      (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
      (h₄ : a₄ = b₄) (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
      E8Z.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ = E8Z.mk b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
    subst h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇; rfl

/-- **(3e) PHI-SHELL IS `Ag`-INVARIANT (the conjugate orbit).**  The outer φ-shell
    is closed under both generators' shell actions: `phiShell` is the complementary
    2I-orbit under `Ag`.  (φ commutes with the action by (3d), so `Ag` carries the
    φ-dilated inner orbit to itself.) -/
theorem phiShell_Ag_closed_gi :
    phiShell.all (fun p => phiShell.contains (Ag gi p)) = true := by decide
theorem phiShell_Ag_closed_gg :
    phiShell.all (fun p => phiShell.contains (Ag gg p)) = true := by decide

-- ══════════════════════════════════════════════════════════
-- §4  MASTER CERTIFICATE — the 2I-equivariant orbit decomposition
-- ══════════════════════════════════════════════════════════

/-- **ICOSIAN-E8-EQUIVARIANCE (master).**  The σ₊⊕σ₋ embedding is 2I-EQUIVARIANT:
    it maps the icosian left-multiplication action to the induced 8×8 ℤ[φ]-matrix
    action `Mg`, and that action's orbit structure is exactly the two-shell
    decomposition of the golden 240.

      (1) SINGLE 2I-ORBIT: `Cover.icosa` is one orbit of `qOne` under left
          multiplication by the generators (spanning tree reaches all 120, and
          `buildNodes`/`icosa` contain each other).
      (2) INTERTWINING: for each generator `g`, `embed (qmulZ g q) = Mg g (embed q)`
          for EVERY ℤ[φ]-quaternion `q` — a polynomial identity (per generator),
          not a 120-enumeration; with `embed` additive.
      (3) ORBIT = SHELL, φ CENTRAL: `innerShell` is the `embed`-image of the single
          orbit and is closed under the shell action `Ag g = halfE8 ∘ Mg g` (both
          generators); `φ·` commutes with `Mg` for EVERY point, so the φ-shell is
          the conjugate `Ag`-orbit and `innerShell ⊎ φ·innerShell` is the
          2I-equivariant orbit decomposition of the 240.

    This UPGRADES `IcosianE8LatticeIso`'s set/shell convergence to an EQUIVARIANT
    map of group actions, tying `SpinorCover600Cell`'s 2I (`hom_bridge`) to the E_8
    golden lattice shell.  It works in the exact golden ℤ[φ]⁸ model; identification
    of `Mg`/`Ag` with the integer-basis E_8 Weyl action inherits the named
    irrational O(8) alignment obligation. -/
theorem equivariance_master :
    -- (1) single 2I-orbit
    (buildNodes.length = 120
      ∧ buildNodes.all (fun a => icosa.contains a) = true
      ∧ icosa.all (fun a => buildNodes.contains a) = true)
    -- (2) raw linear intertwining for both generators, ALL q
    ∧ (∀ q : QZ, embed (qmulZ gi q) = Mg gi (embed q))
    ∧ (∀ q : QZ, embed (qmulZ gg q) = Mg gg (embed q))
    -- (3a) shell-preserving intertwining (×2 group product = Ag), both generators
    ∧ (icosa.all (fun q => decide (embed (qmulS gi q) = Ag gi (embed q))) = true
        ∧ icosa.all (fun q => decide (embed (qmulS gg q) = Ag gg (embed q))) = true)
    -- (3b) inner shell is the orbit image and Ag-closed
    ∧ ((buildNodes.map embed).all (fun p => innerShell.contains p) = true
        ∧ innerShell.all (fun p => (buildNodes.map embed).contains p) = true)
    ∧ (innerShell.all (fun p => innerShell.contains (Ag gi p)) = true
        ∧ innerShell.all (fun p => innerShell.contains (Ag gg p)) = true)
    -- (3c) φ commutes with Mg for EVERY point; φ-shell is Ag-closed (conjugate orbit)
    ∧ (∀ g : QZ, ∀ p : E8Z, phiScaleE8Z (Mg g p) = Mg g (phiScaleE8Z p))
    ∧ (phiShell.all (fun p => phiShell.contains (Ag gi p)) = true
        ∧ phiShell.all (fun p => phiShell.contains (Ag gg p)) = true) := by
  exact ⟨icosa_single_orbit, intertwine_gi, intertwine_gg,
         ⟨intertwine_shell_gi, intertwine_shell_gg⟩,
         innerShell_is_orbit_image,
         ⟨innerShell_Ag_closed_gi, innerShell_Ag_closed_gg⟩,
         phiScale_comm_Mg,
         ⟨phiShell_Ag_closed_gi, phiShell_Ag_closed_gg⟩⟩

-- ══════════════════════════════════════════════════════════
-- §5  Reading
-- ══════════════════════════════════════════════════════════

/-! The σ₊⊕σ₋ embedding MAPS the 2I left-multiplication action onto the induced
    8×8 ℤ[φ]-matrix action `Mg = L(σ₊ g) ⊕ L(σ₋ g)`: `embed ∘ (qmulZ g ·) =
    Mg g ∘ embed` for both generators and ALL `q` (a per-generator polynomial
    identity, not a 120-scan).  Because `Cover.icosa` stores each icosian ×2, the
    GROUP action on the shell is the halved product `qmulS`, realized by
    `Ag g = halfE8 ∘ Mg g` (`embed (qmulS g q) = Ag g (embed q)` on the shell);
    `Cover.icosa` is a SINGLE orbit of `qOne`, so `innerShell = embed '' icosa` is
    one `Ag`-orbit of `embed qOne` (closed under both generators).  The golden
    central scalar `φ` commutes with `Mg` for every point, so the φ-scaled outer
    shell is the conjugate `Ag`-orbit.  This makes `IcosianE8LatticeIso`'s two-shell
    decomposition
    `innerShell ⊎ φ·innerShell` the 2I-EQUIVARIANT orbit structure of the golden
    240 — the same GROUP ACTION on both ends of the convergence, not merely the same
    point set.  All in the exact golden ℤ[φ]⁸ model, no reals.

    -- Next exploration:
    --   (A)  Mg ORTHOGONALITY from the norm.  `Mg g` is the σ₊⊕σ₋ image of a
    --        unit-quaternion left-multiplication, hence an isometry; derive
    --        `normSqZ (Mg g p) = normSqZ p` on the shell as a corollary of the
    --        intertwining + `IcosianE8Embedding.embed_norm_eight`, and (universal
    --        `q`) prove `Mg gᵀ Mg g = I₈` as a polynomial identity by the same
    --        reflection engine — promoting `Mg` from "induced linear map" to a
    --        certified element of O(8, ℤ[φ]).
    --   (B)  GROUP CLOSURE OF Mg.  With the intertwining and `icosa_single_orbit`,
    --        the matrices `{Mg g : g ∈ icosa}` form a group ≅ 2I acting on the
    --        shell; prove `Mg`-multiplicativity `Mg (qmulZ g h) = mmul8 (Mg g)
    --        (Mg h)` (the 8×8 analogue of `hom_bridge`) so the 120 matrices are a
    --        faithful 8-dim representation of 2I — the Weyl-subgroup action in
    --        golden coordinates.
    --   (C)  INTEGER-BASIS WEYL ACTION.  Identify the `Mg`-action with a subgroup of
    --        the integer-basis E_8 Weyl group on `E8Lattice.e8Roots` — the same
    --        irrational O(8) alignment named in `IcosianE8LatticeIso` (A); the
    --        golden equivariance proved here is the Init-only half, the integer
    --        identification the real-analytic completion.
-/

end IcosianE8Equivariance
end Gnosis

/-! ## Axiom footprint (verified) — see `#print axioms` below. -/

#print axioms Gnosis.IcosianE8Equivariance.icosa_single_orbit
#print axioms Gnosis.IcosianE8Equivariance.intertwine_gi
#print axioms Gnosis.IcosianE8Equivariance.intertwine_gg
#print axioms Gnosis.IcosianE8Equivariance.embed_add
#print axioms Gnosis.IcosianE8Equivariance.intertwine_shell_gi
#print axioms Gnosis.IcosianE8Equivariance.innerShell_is_orbit_image
#print axioms Gnosis.IcosianE8Equivariance.innerShell_Ag_closed_gi
#print axioms Gnosis.IcosianE8Equivariance.phiScale_comm_Mg
#print axioms Gnosis.IcosianE8Equivariance.phiShell_Ag_closed_gi
#print axioms Gnosis.IcosianE8Equivariance.equivariance_master
