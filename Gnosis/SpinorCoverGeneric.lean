/-
  SpinorCoverGeneric.lean
  =======================

  THE RING-GENERIC UNIVERSAL HOMOMORPHISM for the SU(2) → SO(3) conjugation cover, proved
  ONCE over an ARBITRARY commutative ring `GR.CRing R`, so that the per-ring `hom_bridge`
  proofs of `SpinorCover600Cell` (ℤ[φ]), `SpinorCover2O` (ℤ[√2]), and the Int case all become
  INSTANCES of a single theorem. This formalizes the standing observation (the `Next
  exploration` of `SpinorCover2O`) that every per-ring `hom_bridge` proof is "line-for-line
  identical, only the ring swaps."

  ── WHAT IS RING-FREE, AND WHAT IS NOT (the honest decomposition) ───────────────────────────

  The conjugation-to-rotation map `R(q) = q·v·q⁻¹` (matrix form, scaled by |q|²) satisfies the
  homomorphism `R(p·q) = R(p)·R(q)` as a POLYNOMIAL IDENTITY in the eight quaternion
  components. The proof factors into two layers:

    LAYER A — the algebraic lift (FULLY ring-generic, proved here ONCE).
      Given a commutative ring `K : GR.CRing R` and the nine normal-form entry equalities
      `reify K (R_ij(p·q)) = reify K (Σ_k R_ik(p) R_kj(q))`, the homomorphism
      `RmatOver K (qmulOver K p q) = mmulOver K (RmatOver K p) (RmatOver K q)` follows for
      EVERY pair of `R`-quaternions, by `GR.denote_eq_of_reify_eq` instantiated at `K` and a
      single structural unfolding. This is `hom_bridge_generic_of` — the one theorem the six
      covers share. It is `∀ {R} [GR.CRing R], (nine reify identities) → (homomorphism)`.

    LAYER B — the nine normal-form equalities (ring-SPECIFIC `decide`, NOT ring-free).
      `reify K e₁ = reify K e₂` is an equality of `Poly R` normal forms whose COEFFICIENTS are
      built from `K.one`, `K.add`, `K.mul`; the reflective normalizer's zero-test calls
      `K`'s `DecidableEq`. So the nine equalities hold for every ring but must be re-checked by
      kernel `decide` over each CONCRETE `K` (no `DecidableEq`/computation exists for an
      abstract `K`). This is exactly why a hypothesis-FREE `∀ {R} [GR.CRing R]` bridge cannot
      be stated at the abstract ring — and we say so, rather than fake it. The shapes are
      identical across rings (see `SpinorCover600Cell.e00..e22` vs `SpinorCover2O.e00..e22`,
      character-for-character the same), so the per-ring cost is ONLY the nine `decide`s.

  ── THE PAYOFF ─────────────────────────────────────────────────────────────────────────────

  Each per-ring `hom_bridge` reduces to: supply the nine `decide`d identities, apply
  `hom_bridge_generic_of`. We exhibit:
    * `hom_bridge_zphi`  — ℤ[φ], matching `SpinorCover600Cell.hom_bridge` (the 2I carrier).
    * `hom_bridge_zsqrt2` — ℤ[√2], matching `SpinorCover2O.hom_bridge2` (the 2O/2C4/2D4 carrier).
    * `hom_bridge_int`    — Int, the Q8/2T carrier.
  and cite that the existing per-ring statements are these instances. (We do NOT edit the
  other modules; we DEMONSTRATE the instantiation.)

  `spinor_cover_generic_master` records the structural fact: the conjugation cover is a
  homomorphism over EVERY commutative ring (one theorem `hom_bridge_generic_of`), so each
  binary polyhedral / cyclic / dihedral cover reduces to closure + kernel over that single
  identity — the six covers Q8 / 2T / 2O / 2I / 2C4 / 2D4 are all instances of it (three
  distinct carrier rings: Int, ℤ[√2], ℤ[φ]).

  ── CONSTRAINTS (met) ──────────────────────────────────────────────────────────────────────

  Init-only (`import Init` + the cited Gnosis cover bridges, which are themselves Init-only).
  Kernel `decide` / `rfl` / structural + the `GR.reify` reflection engine ONLY — NO
  `native_decide`, no `sorry`, no `admit`, no new `axiom`, no `Classical.choice`, no `omega`.
  `set_option maxRecDepth` raised (the normalizer recurses through degree-4 polynomials in 8
  variables). Gate ONLY on `lake build Gnosis.SpinorCoverGeneric`. Does NOT edit other modules
  and does NOT register itself in `Gnosis.lean` (the orchestrator does that). `#print axioms`
  for `hom_bridge_generic_of` and the master are at the bottom.

  RELATIONSHIP, STATED PRECISELY. `hom_bridge_generic_of` is NOT a new mathematical claim; it
  is the COMMON GENERALIZATION of the three computed per-ring bridges — it abstracts their
  shared proof to `GR.CRing R` and recovers each by instantiation. It does not establish the
  continuous SU(2) → SO(3) surjectivity (that remains the Mathlib deferral in the per-ring
  modules); it formalizes that the finite-restriction homomorphism is ONE ring-generic fact.
-/

import Init
import Gnosis.SpinorCover600Cell
import Gnosis.SpinorCover2O

-- The reflective normalizer recurses through degree-4 polynomials in 8 variables; raise the
-- reduction depth. DEPTH knob only — still pure kernel `decide`, no `native_decide`.
set_option maxRecDepth 8000

-- Cosmetic linters only (the generic engine carries `[DecidableEq R]` for the normalizer; a
-- few generic sub-defs don't use the instance directly).
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace SpinorCoverGeneric

open GR

-- ════════════════════════════════════════════════════════════════════════════════════════
-- §1  GENERIC CARRIER: quaternions, conjugation rotation, matrix product over ANY `CRing R`
-- ════════════════════════════════════════════════════════════════════════════════════════

/-- A quaternion with components in an arbitrary carrier `R`. -/
structure QuatG (R : Type) where
  w : R
  x : R
  y : R
  z : R

/-- A 3×3 matrix with entries in an arbitrary carrier `R`. -/
structure M3G (R : Type) where
  a00 : R
  a01 : R
  a02 : R
  a10 : R
  a11 : R
  a12 : R
  a20 : R
  a21 : R
  a22 : R

variable {R : Type} [DecidableEq R]

/-- Hamilton quaternion product over `K` (the scaled cover convention used per-ring:
    `SpinorCover600Cell.qmulZ` / `SpinorCover2O.qmulZ` are this with `K = Kz` / `Kz2`). -/
def qmulOver (K : CRing R) (p q : QuatG R) : QuatG R :=
  let sub a b := K.add a (K.neg b)
  { w := sub (sub (sub (K.mul p.w q.w) (K.mul p.x q.x)) (K.mul p.y q.y)) (K.mul p.z q.z)
  , x := K.add (K.add (K.mul p.w q.x) (K.mul p.x q.w)) (sub (K.mul p.y q.z) (K.mul p.z q.y))
  , y := K.add (sub (K.mul p.w q.y) (K.mul p.x q.z)) (K.add (K.mul p.y q.w) (K.mul p.z q.x))
  , z := K.add (sub (K.add (K.mul p.w q.z) (K.mul p.x q.y)) (K.mul p.y q.x)) (K.mul p.z q.w) }

/-- The conjugation rotation matrix (scaled by |q|²) over `K`. `2` is `K.one + K.one`.
    Matches `SpinorCover600Cell.RmatZ` / `SpinorCover2O.RmatZ` with `K = Kz` / `Kz2`. -/
def RmatOver (K : CRing R) (q : QuatG R) : M3G R :=
  let sub a b := K.add a (K.neg b)
  let two := K.add K.one K.one
  let dbl p := K.mul two p
  let a := q.w; let b := q.x; let cc := q.y; let d := q.z
  { a00 := sub (sub (K.add (K.mul a a) (K.mul b b)) (K.mul cc cc)) (K.mul d d)
  , a01 := dbl (sub (K.mul b cc) (K.mul a d))
  , a02 := dbl (K.add (K.mul b d) (K.mul a cc))
  , a10 := dbl (K.add (K.mul b cc) (K.mul a d))
  , a11 := sub (K.add (sub (K.mul a a) (K.mul b b)) (K.mul cc cc)) (K.mul d d)
  , a12 := dbl (sub (K.mul cc d) (K.mul a b))
  , a20 := dbl (sub (K.mul b d) (K.mul a cc))
  , a21 := dbl (K.add (K.mul cc d) (K.mul a b))
  , a22 := sub (sub (K.add (K.mul a a) (K.mul d d)) (K.mul b b)) (K.mul cc cc) }

/-- 3×3 matrix product over `K`. Matches `SpinorCover600Cell.mmulZ` / `SpinorCover2O.mmulZ`. -/
def mmulOver (K : CRing R) (P Q : M3G R) : M3G R :=
  { a00 := K.add (K.add (K.mul P.a00 Q.a00) (K.mul P.a01 Q.a10)) (K.mul P.a02 Q.a20)
  , a01 := K.add (K.add (K.mul P.a00 Q.a01) (K.mul P.a01 Q.a11)) (K.mul P.a02 Q.a21)
  , a02 := K.add (K.add (K.mul P.a00 Q.a02) (K.mul P.a01 Q.a12)) (K.mul P.a02 Q.a22)
  , a10 := K.add (K.add (K.mul P.a10 Q.a00) (K.mul P.a11 Q.a10)) (K.mul P.a12 Q.a20)
  , a11 := K.add (K.add (K.mul P.a10 Q.a01) (K.mul P.a11 Q.a11)) (K.mul P.a12 Q.a21)
  , a12 := K.add (K.add (K.mul P.a10 Q.a02) (K.mul P.a11 Q.a12)) (K.mul P.a12 Q.a22)
  , a20 := K.add (K.add (K.mul P.a20 Q.a00) (K.mul P.a21 Q.a10)) (K.mul P.a22 Q.a20)
  , a21 := K.add (K.add (K.mul P.a20 Q.a01) (K.mul P.a21 Q.a11)) (K.mul P.a22 Q.a21)
  , a22 := K.add (K.add (K.mul P.a20 Q.a02) (K.mul P.a21 Q.a12)) (K.mul P.a22 Q.a22) }

-- ════════════════════════════════════════════════════════════════════════════════════════
-- §2  GENERIC ENTRY EXPRESSIONS in `@PExpr R` (the SAME nine shapes used per-ring)
-- ════════════════════════════════════════════════════════════════════════════════════════
-- The eight component variables (var 0..3 = p, var 4..7 = q) and the matrix-entry / product
-- expression families, built over `@PExpr R`. The ONLY ring-touching atom is the constant
-- `2`, written ring-generically as `one + one` so the same builder serves every `K`.

abbrev PE (R : Type) := @PExpr R

def vw : PE R := .var 0
def vx : PE R := .var 1
def vy : PE R := .var 2
def vz : PE R := .var 3
def vW : PE R := .var 4
def vX : PE R := .var 5
def vY : PE R := .var 6
def vZ : PE R := .var 7
/-- `2` as a `PExpr`, ring-generically: `K.one + K.one`. `denote K env c2 = K.add K.one K.one`. -/
def c2 (K : CRing R) : PE R := .add (.cst K.one) (.cst K.one)

def pqw : PE R := .sub (.sub (.sub (.mul vw vW) (.mul vx vX)) (.mul vy vY)) (.mul vz vZ)
def pqx : PE R := .add (.add (.mul vw vX) (.mul vx vW)) (.sub (.mul vy vZ) (.mul vz vY))
def pqy : PE R := .add (.sub (.mul vw vY) (.mul vx vZ)) (.add (.mul vy vW) (.mul vz vX))
def pqz : PE R := .add (.sub (.add (.mul vw vZ) (.mul vx vY)) (.mul vy vX)) (.mul vz vW)

def R00 (a b cc d : PE R) : PE R := .sub (.sub (.add (.mul a a) (.mul b b)) (.mul cc cc)) (.mul d d)
def R01 (K : CRing R) (a b cc d : PE R) : PE R := .mul (c2 K) (.sub (.mul b cc) (.mul a d))
def R02 (K : CRing R) (a b cc d : PE R) : PE R := .mul (c2 K) (.add (.mul b d) (.mul a cc))
def R10 (K : CRing R) (a b cc d : PE R) : PE R := .mul (c2 K) (.add (.mul b cc) (.mul a d))
def R11 (a b cc d : PE R) : PE R := .sub (.add (.sub (.mul a a) (.mul b b)) (.mul cc cc)) (.mul d d)
def R12 (K : CRing R) (a b cc d : PE R) : PE R := .mul (c2 K) (.sub (.mul cc d) (.mul a b))
def R20 (K : CRing R) (a b cc d : PE R) : PE R := .mul (c2 K) (.sub (.mul b d) (.mul a cc))
def R21 (K : CRing R) (a b cc d : PE R) : PE R := .mul (c2 K) (.add (.mul cc d) (.mul a b))
def R22 (a b cc d : PE R) : PE R := .sub (.sub (.add (.mul a a) (.mul d d)) (.mul b b)) (.mul cc cc)

/-- product-matrix entry `(i,j) = Σ_k R_ik(p) · R_kj(q)`, generic over `R`. -/
def prodEntry (Ri0 Ri1 Ri2 : PE R → PE R → PE R → PE R → PE R)
              (R0j R1j R2j : PE R → PE R → PE R → PE R → PE R) : PE R :=
  .add (.add (.mul (Ri0 vw vx vy vz) (R0j vW vX vY vZ))
             (.mul (Ri1 vw vx vy vz) (R1j vW vX vY vZ)))
       (.mul (Ri2 vw vx vy vz) (R2j vW vX vY vZ))

-- ════════════════════════════════════════════════════════════════════════════════════════
-- §3  THE GENERIC BRIDGE (Layer A) — proved ONCE over any `CRing R`
-- ════════════════════════════════════════════════════════════════════════════════════════

/-- environment built from a concrete generic-quaternion pair (var 0..3 = p, var 4..7 = q). -/
def qenvG (K : CRing R) (p q : QuatG R) : Nat → R :=
  fun i => [p.w, p.x, p.y, p.z, q.w, q.x, q.y, q.z].getD i K.zero

/-- **THE RING-GENERIC UNIVERSAL HOMOMORPHISM (Layer A).**

    Over ANY commutative ring `K : GR.CRing R`, given the nine normal-form entry equalities
    `reify K (R_ij(p·q)) = reify K (Σ_k R_ik(p) R_kj(q))`, the conjugation map is a
    homomorphism: `RmatOver K (qmulOver K p q) = mmulOver K (RmatOver K p) (RmatOver K q)`
    for every pair of `R`-quaternions.

    This is the ONE theorem the six covers share. The nine hypotheses are exactly the per-ring
    `e00..e22` (the same `PExpr` shapes for every ring; each ring discharges them by `decide`).
    The proof is `GR.denote_eq_of_reify_eq` instantiated at the abstract `K` on each entry,
    then a single structural unfolding — line-for-line the per-ring `hom_bridge` body, with the
    ring abstracted. -/
theorem hom_bridge_generic_of (K : CRing R)
    (h00 : reify K (R00 (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry R00 (R01 K) (R02 K) R00 (R10 K) (R20 K)))
    (h01 : reify K (R01 K (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry R00 (R01 K) (R02 K) (R01 K) R11 (R21 K)))
    (h02 : reify K (R02 K (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry R00 (R01 K) (R02 K) (R02 K) (R12 K) R22))
    (h10 : reify K (R10 K (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry (R10 K) R11 (R12 K) R00 (R10 K) (R20 K)))
    (h11 : reify K (R11 (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry (R10 K) R11 (R12 K) (R01 K) R11 (R21 K)))
    (h12 : reify K (R12 K (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry (R10 K) R11 (R12 K) (R02 K) (R12 K) R22))
    (h20 : reify K (R20 K (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry (R20 K) (R21 K) R22 R00 (R10 K) (R20 K)))
    (h21 : reify K (R21 K (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry (R20 K) (R21 K) R22 (R01 K) R11 (R21 K)))
    (h22 : reify K (R22 (pqw) (pqx) (pqy) (pqz))
         = reify K (prodEntry (R20 K) (R21 K) R22 (R02 K) (R12 K) R22))
    (p q : QuatG R) :
    RmatOver K (qmulOver K p q) = mmulOver K (RmatOver K p) (RmatOver K q) := by
  have E00 := denote_eq_of_reify_eq K _ _ h00 (qenvG K p q)
  have E01 := denote_eq_of_reify_eq K _ _ h01 (qenvG K p q)
  have E02 := denote_eq_of_reify_eq K _ _ h02 (qenvG K p q)
  have E10 := denote_eq_of_reify_eq K _ _ h10 (qenvG K p q)
  have E11 := denote_eq_of_reify_eq K _ _ h11 (qenvG K p q)
  have E12 := denote_eq_of_reify_eq K _ _ h12 (qenvG K p q)
  have E20 := denote_eq_of_reify_eq K _ _ h20 (qenvG K p q)
  have E21 := denote_eq_of_reify_eq K _ _ h21 (qenvG K p q)
  have E22 := denote_eq_of_reify_eq K _ _ h22 (qenvG K p q)
  cases p; cases q
  simp only [RmatOver, mmulOver, qmulOver, qenvG, List.getD,
             denote, R00, R01, R02, R10, R11, R12, R20, R21, R22,
             prodEntry, pqw, pqx, pqy, pqz, vw, vx, vy, vz, vW, vX, vY, vZ, c2] at *
  refine M3G.mk.injEq .. ▸ ?_
  refine ⟨E00, E01, E02, E10, E11, E12, E20, E21, E22⟩

-- ════════════════════════════════════════════════════════════════════════════════════════
-- §4  PER-RING INSTANCES (Layer B) — discharge the nine `decide`s, apply the generic bridge
-- ════════════════════════════════════════════════════════════════════════════════════════
-- Each ring supplies its own nine normal-form equalities by kernel `decide` over its concrete
-- `K`, then `hom_bridge_generic_of` yields the per-ring homomorphism. These reproduce — by
-- INSTANTIATION of the single generic theorem — the existing `SpinorCover600Cell.hom_bridge`
-- (ℤ[φ]), `SpinorCover2O.hom_bridge2` (ℤ[√2]), and the Int (Q8/2T) bridge.

open ZPhi ZSqrt2 IntInst

/-- **ℤ[φ] instance.** The generic bridge specialized to the golden-ratio ring `Kz` — the 2I
    (600-cell / E8) carrier. Same statement as `SpinorCover600Cell.hom_bridge` modulo the
    generic-vs-bespoke carrier names; it follows from `hom_bridge_generic_of` by supplying the
    nine ℤ[φ] `decide`s. -/
theorem hom_bridge_zphi (p q : QuatG Zphi) :
    RmatOver Kz (qmulOver Kz p q) = mmulOver Kz (RmatOver Kz p) (RmatOver Kz q) :=
  hom_bridge_generic_of Kz
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) p q

/-- **ℤ[√2] instance.** The generic bridge specialized to `Kz2` — the carrier shared by 2O,
    2C4, and 2D4. Same statement as `SpinorCover2O.hom_bridge2`; it follows from
    `hom_bridge_generic_of` by supplying the nine ℤ[√2] `decide`s. -/
theorem hom_bridge_zsqrt2 (p q : QuatG Zs2) :
    RmatOver Kz2 (qmulOver Kz2 p q) = mmulOver Kz2 (RmatOver Kz2 p) (RmatOver Kz2 q) :=
  hom_bridge_generic_of Kz2
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) p q

/-- **Int instance.** The generic bridge specialized to `Ki` — the Lipschitz-integer carrier
    of Q8 and 2T. It follows from `hom_bridge_generic_of` by supplying the nine ℤ `decide`s. -/
theorem hom_bridge_int (p q : QuatG Int) :
    RmatOver Ki (qmulOver Ki p q) = mmulOver Ki (RmatOver Ki p) (RmatOver Ki q) :=
  hom_bridge_generic_of Ki
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) p q

-- ════════════════════════════════════════════════════════════════════════════════════════
-- §5  MASTER — one homomorphism over every ring; the six covers are its instances
-- ════════════════════════════════════════════════════════════════════════════════════════

/-- **THE GENERIC-COVER MASTER.** The SU(2) → SO(3) conjugation cover is a homomorphism over
    EVERY commutative ring — `hom_bridge_generic_of`, ONE theorem — so each binary
    polyhedral / cyclic / dihedral cover reduces to closure + kernel over that single identity.
    The six computed covers are all instances, across exactly three carrier rings:

      • Int    `Ki`  → Q8 (= 2D2), 2T          (`hom_bridge_int`)
      • ℤ[√2]  `Kz2` → 2O, 2C4, 2D4            (`hom_bridge_zsqrt2`)
      • ℤ[φ]   `Kz`  → 2I (600-cell / E8)      (`hom_bridge_zphi`)

    We bundle the three carrier instances; each is `hom_bridge_generic_of` applied to that
    ring's nine `decide`d entry identities, witnessing that the per-ring `hom_bridge`s are
    literally instances of the one generic bridge. -/
theorem spinor_cover_generic_master :
    (∀ p q : QuatG Int,  RmatOver Ki  (qmulOver Ki  p q) = mmulOver Ki  (RmatOver Ki  p) (RmatOver Ki  q))
    ∧ (∀ p q : QuatG Zs2,  RmatOver Kz2 (qmulOver Kz2 p q) = mmulOver Kz2 (RmatOver Kz2 p) (RmatOver Kz2 q))
    ∧ (∀ p q : QuatG Zphi, RmatOver Kz  (qmulOver Kz  p q) = mmulOver Kz  (RmatOver Kz  p) (RmatOver Kz  q)) :=
  ⟨hom_bridge_int, hom_bridge_zsqrt2, hom_bridge_zphi⟩

end SpinorCoverGeneric

/-! ## Axiom footprint (verified)

`#print axioms` on the headline theorems. The generic bridge and its instances depend on at
most `propext` + `Quot.sound` (the standard Init kernel axioms used by `decide`/`simp`) —
propext-at-most, NO `Classical.choice`:

    SpinorCoverGeneric.hom_bridge_generic_of        -- [propext, Quot.sound]
    SpinorCoverGeneric.spinor_cover_generic_master  -- [propext, Quot.sound]
    SpinorCoverGeneric.hom_bridge_zphi              -- [propext, Quot.sound]
    SpinorCoverGeneric.hom_bridge_zsqrt2            -- [propext, Quot.sound]
    SpinorCoverGeneric.hom_bridge_int               -- [propext, Quot.sound]

No `native_decide`, no `sorry`, no `admit`, no new `axiom`, no `Classical.choice`, no `omega`.
-/

#print axioms SpinorCoverGeneric.hom_bridge_generic_of
#print axioms SpinorCoverGeneric.spinor_cover_generic_master
#print axioms SpinorCoverGeneric.hom_bridge_zphi
#print axioms SpinorCoverGeneric.hom_bridge_zsqrt2
#print axioms SpinorCoverGeneric.hom_bridge_int

/-! ## Next exploration

The generic bridge `hom_bridge_generic_of` makes a new finite SU(2) subgroup cover cost ONLY
its carrier ring instance + closure list + kernel scan. The natural next target is the GENERAL
binary CYCLIC family 2Cₙ (and binary dihedral 2Dₙ) for arbitrary `n` — now nearly trivial:

  * Binary cyclic 2Cₙ lives in the cyclotomic ring ℤ[ζ_{2n}] (ζ = primitive 2n-th root). Build
    the `GR.CRing` instance for ℤ[ζ_{2n}] by the same Int-reflection helper (`GR.IntInst.Ki`)
    used for ℤ[φ] and ℤ[√2] — a degree-φ(2n) coefficient vector with the cyclotomic
    multiplication table. Then 2Cₙ's homomorphism is `hom_bridge_generic_of` at that ring; the
    only per-`n` work is the nine `decide`s (same shapes) plus the `n`-element rotation list
    and the `{±1}` kernel scan. No new `hom_bridge` proof per `n`.

  * Push genericity one layer deeper: parameterize the nine `reify`-equalities themselves by a
    UNIFORM coefficient model so a single meta-`decide` discharges them for a whole cyclotomic
    family at once (the normal-form coefficients are integer combinations of `one`; the only
    `n`-dependence is the minimal-polynomial reduction). That would collapse Layer B from
    "nine `decide`s per ring" to "one `decide` per minimal polynomial," making the entire
    binary-ADE + cyclotomic ladder a single parameterized theorem.

  * Continuum lift (unchanged deferral, needs Mathlib): realize each `RmatOver K` as the finite
    restriction of the continuous Lie cover SU(2) → SO(3); the hard part remains real-manifold
    surjectivity, independent of this algebraic genericity.
-/
