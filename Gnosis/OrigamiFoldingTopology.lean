/-
  OrigamiFoldingTopology.lean
  ===========================

  A finite math model of folding: the physical incompressibility of paper, the
  Gallivan fold limit across paper sizes, the Betti length of famous origami
  crease patterns, and the proof that *continuity conceals information*.

  This module sits downstream of three siblings and speaks their language:

    - `Gnosis/Origami.lean` gives the RULES of origami as finite carriers
      (Maekawa's parity, Kawasaki's 360, the seven Huzita-Hatori folds,
      layer two-colorability). We import and re-export the parity rule and
      tie it to the crease-graph Betti below.

    - `Gnosis/KnotRopelengthComplexity.lean` fixes the convention
      `ropelength = total Betti` over a `BettiSig = List Nat`. We reuse that
      so an origami shape's "Betti length" is literally a ropelength.

    - `Gnosis/BashoClinamenFoldingInvariant.lean` shows the haiku (folded) and
      the American sentence (unfolded) share ropelength 17, and that folding
      preserves the Betti charge while redistributing it across pauses. The
      crane's crease-graph Betti length below lands on 17 by the same count —
      the orizuru ties the same rope the haiku does.

  The physics enters only as finite certificates (Rustic Church bridge rule):
  paper thickness, sheet length, and the Gallivan minimum-length law are
  represented as exact `Nat` inequalities scaled to clear the `π/6` constant,
  and every empirical "you cannot fold it again" is a closed `native_decide`
  on integers — never a smuggled physical claim.

  Init-only. No Mathlib. No `omega`. No `simp`/`decide` on open-variable goals.
  Closed numerics use `decide` / `native_decide` (Rustic Church admits these on
  goals with no free variables).
-/
import Init
import Gnosis.Origami
import Gnosis.KnotRopelengthComplexity

namespace GnosisMath
namespace OrigamiFoldingTopology

-- ══════════════════════════════════════════════════════════
-- PART I.  LAYER DOUBLING  (the physical incompressibility core)
-- ══════════════════════════════════════════════════════════

/-- Folding a sheet in half doubles the number of stacked layers.
    After `n` folds there are `2^n` layers. This is the irreducible engine
    of incompressibility: the material that must bend through the crease
    radius doubles every fold. -/
def layers (n : Nat) : Nat := 2 ^ n

/-- Each fold doubles the layer count. -/
theorem layers_succ (n : Nat) : layers (n + 1) = 2 * layers n := by
  unfold layers
  rw [Nat.pow_succ, Nat.mul_comm]

/-- There is always at least one layer (the sheet itself). -/
theorem layers_pos : ∀ n, 0 < layers n
  | 0 => by decide
  | n + 1 => by
      rw [layers_succ]
      exact Nat.mul_pos (by decide) (layers_pos n)

/-- Every fold strictly increases the layer count: folding is monotone. -/
theorem layers_strict_mono (n : Nat) : layers n < layers (n + 1) := by
  rw [layers_succ, Nat.two_mul]
  exact Nat.lt_add_of_pos_left (layers_pos n)

/-- Non-strict monotonicity of layers. -/
theorem layers_le_succ (n : Nat) : layers n ≤ layers (n + 1) :=
  Nat.le_of_lt (layers_strict_mono n)

/-- After at least one fold there are at least two layers. -/
theorem one_lt_layers_succ (n : Nat) : 1 < layers (n + 1) := by
  rw [layers_succ]
  have h : (2 : Nat) * 1 ≤ 2 * layers n :=
    Nat.mul_le_mul (Nat.le_refl 2) (layers_pos n)
  exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2 * 1) h

/-- The stack thickness after `n` folds: original thickness `t` times layers. -/
def stackThickness (t n : Nat) : Nat := t * layers n

/-- Stack thickness doubles every fold — the geometric blow-up that no
    amount of pressing can compress away. -/
theorem stackThickness_succ (t n : Nat) :
    stackThickness t (n + 1) = 2 * stackThickness t n := by
  unfold stackThickness
  rw [layers_succ, ← Nat.mul_assoc, Nat.mul_comm t 2, Nat.mul_assoc]

-- ══════════════════════════════════════════════════════════
-- PART II.  THE GALLIVAN FOLD LIMIT  (single-direction folding)
-- ══════════════════════════════════════════════════════════

/-
  Britney Gallivan's single-direction folding law (2002): to fold a strip of
  thickness `t` in half `n` times, the minimum starting length is

        L_min = (π·t/6) · (2^n + 4) · (2^n − 1).

  Each fold loses a half-circle of material at the crease whose radius grows
  with the current stack thickness, so the length consumed grows like the
  product below. To stay exact in `Nat` we clear the `π/6` constant:
  `π/6 ≈ 0.5235987…`, and `1309/2500 = 0.5236`, a tight rational over-estimate
  (it demands marginally more length, so feasibility verdicts are conservative).

  A fold of `n` is FEASIBLE for length `L`, thickness `t` iff

        piSixNum · t · foldFactor n  ≤  piSixDen · L      (all in microns).
-/

/-- Numerator of the `π/6` rational over-estimate. -/
def piSixNum : Nat := 1309
/-- Denominator of the `π/6` rational over-estimate. -/
def piSixDen : Nat := 2500

/-- The Gallivan geometric factor `(2^n + 4)(2^n − 1)`.
    Zero at `n = 0` (folding zero times is free). -/
def foldFactor (n : Nat) : Nat := (layers n + 4) * (layers n - 1)

/-- The factor is monotone in the number of folds: each additional fold
    demands at least as much length. -/
theorem foldFactor_mono (n : Nat) : foldFactor n ≤ foldFactor (n + 1) := by
  unfold foldFactor
  have h1 : layers n + 4 ≤ layers (n + 1) + 4 :=
    Nat.add_le_add_right (layers_le_succ n) 4
  have h2 : layers n - 1 ≤ layers (n + 1) - 1 :=
    Nat.sub_le_sub_right (layers_le_succ n) 1
  exact Nat.mul_le_mul h1 h2

/-- Feasibility predicate (scaled, exact-integer Gallivan law). -/
def foldFeasible (lengthMicrons thickMicrons n : Nat) : Bool :=
  decide (piSixNum * thickMicrons * foldFactor n ≤ piSixDen * lengthMicrons)

-- ══════════════════════════════════════════════════════════
-- PART III.  PAPER SIZES  (physical incompressibility, by size)
-- ══════════════════════════════════════════════════════════

/-
  All dimensions in microns. Standard copy paper thickness ≈ 0.1 mm = 100 µm.
  Single-direction folding uses the LONG dimension. For each common size we
  certify the exact fold at which the sheet stops being foldable — the
  incompressibility wall — by a closed `native_decide`.
-/

/-- US Letter, long side 11 in = 279.4 mm. -/
def letterLen : Nat := 279400
/-- US Legal, long side 14 in = 355.6 mm. -/
def legalLen : Nat := 355600
/-- ISO A4, long side 297 mm. -/
def a4Len : Nat := 297000
/-- ISO A3, long side 420 mm. -/
def a3Len : Nat := 420000
/-- ISO A0, long side 1189 mm. -/
def a0Len : Nat := 1189000
/-- Tabloid / ANSI B, long side 17 in = 431.8 mm. -/
def tabloidLen : Nat := 431800
/-- Gallivan's record roll: ~1.2 km of thin paper. -/
def gallivanRollLen : Nat := 1200000000

/-- Standard copy-paper thickness, 0.1 mm. -/
def copyThick : Nat := 100
/-- Thin tissue thickness (Gallivan's roll), 0.08 mm. -/
def tissueThick : Nat := 80

-- ── The headline: 8.5 × 11 cannot be folded seven times. ──

/-- US Letter folds six times. -/
theorem letter_can_fold_six :
    foldFeasible letterLen copyThick 6 = true := by native_decide

/-- US Letter cannot be folded a seventh time: 7+ is physically impossible. -/
theorem letter_cannot_fold_seven :
    foldFeasible letterLen copyThick 7 = false := by native_decide

/-- The incompressibility wall for Letter sits exactly at fold 7:
    the sixth fold is the last one. -/
theorem letter_incompressibility_wall :
    foldFeasible letterLen copyThick 6 = true ∧
    foldFeasible letterLen copyThick 7 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ── The same wall, located for each common size. ──

theorem legal_wall :
    foldFeasible legalLen copyThick 6 = true ∧
    foldFeasible legalLen copyThick 7 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

theorem a4_wall :
    foldFeasible a4Len copyThick 6 = true ∧
    foldFeasible a4Len copyThick 7 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

theorem a3_wall :
    foldFeasible a3Len copyThick 6 = true ∧
    foldFeasible a3Len copyThick 7 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- A0 is large enough to reach the seventh fold before its wall. -/
theorem a0_wall :
    foldFeasible a0Len copyThick 7 = true ∧
    foldFeasible a0Len copyThick 8 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

theorem tabloid_wall :
    foldFeasible tabloidLen copyThick 6 = true ∧
    foldFeasible tabloidLen copyThick 7 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- Gallivan's roll reaches twelve folds — and not thirteen. This reproduces
    the 2002 record from the exact-integer law alone. -/
theorem gallivan_record_is_twelve :
    foldFeasible gallivanRollLen tissueThick 12 = true ∧
    foldFeasible gallivanRollLen tissueThick 13 = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART IV.  ORIGAMI RULES  (re-exported from Gnosis/Origami.lean)
-- ══════════════════════════════════════════════════════════

/-- Maekawa's parity, restated here: a flat-foldable vertex has even crease
    degree (`M − V = ±2 ⇒ M + V` is even). Proof delegated to the rule module. -/
theorem flatfoldable_vertex_even_degree
    (v : GnosisMath.Origami.CreaseVertex)
    (h : GnosisMath.Origami.satisfiesMaekawa v) :
    (v.mountains + v.valleys) % 2 = 0 :=
  GnosisMath.Origami.degree_is_even_if_maekawa v h

/-- Kawasaki's condition, restated: alternating angle sums are 180 + 180. -/
theorem flatfoldable_vertex_kawasaki
    (v : GnosisMath.Origami.VertexAngles)
    (h : GnosisMath.Origami.satisfiesKawasaki v) :
    v.alphaOddSum + v.alphaEvenSum = 360 :=
  GnosisMath.Origami.kawasaki_implies_360 v h

-- ══════════════════════════════════════════════════════════
-- PART V.  BETTI LENGTH OF A CREASE PATTERN
-- ══════════════════════════════════════════════════════════

/-
  A flat crease pattern is a connected planar graph drawn on the square:
  vertices `V` (paper corners, edge reference points, interior crossings),
  edges `E` (boundary segments + creases), faces `F` (the panels plus the
  outer face). Euler's relation for a connected planar graph is `V − E + F = 2`,
  stated additively as `V + F = E + 1 + 1` to stay in `Nat`.

  The Betti numbers of the crease GRAPH (its 1-skeleton):
    β₀ = 1            (one connected sheet)
    β₁ = E − V + 1    (independent crease cycles = bounded panels)

  Following `KnotRopelengthComplexity`, the "Betti length" is the total Betti =
  ropelength of the signature `[β₀, β₁]`.
-/

/-- A connected planar crease pattern as a finite Euler carrier. -/
structure CreaseGraph where
  V : Nat
  E : Nat
  F : Nat
  euler : V + F = E + 1 + 1

/-- β₀ of a connected crease pattern. -/
def betti0 (_g : CreaseGraph) : Nat := 1

/-- β₁ = cycle rank = E − V + 1 (the number of bounded panels). -/
def betti1 (g : CreaseGraph) : Nat := g.E + 1 - g.V

/-- Betti length = total Betti = β₀ + β₁. -/
def bettiLength (g : CreaseGraph) : Nat := betti0 g + betti1 g

/-- The Betti length is exactly the face count: every panel (and the outer
    face) contributes one unit of rope. This is Euler's relation made into a
    ropelength identity, proved Init-only. -/
theorem bettiLength_eq_faces (g : CreaseGraph) (hF : 1 ≤ g.F) :
    bettiLength g = g.F := by
  unfold bettiLength betti0 betti1
  have hEuler := g.euler
  -- V ≤ E + 1, since V + 1 ≤ V + F = E + 1 + 1.
  have hV : g.V ≤ g.E + 1 := by
    have h1 : g.V + 1 ≤ g.V + g.F := Nat.add_le_add_left hF g.V
    rw [hEuler] at h1
    exact Nat.le_of_add_le_add_right h1
  -- (E + 1 − V) + V = E + 1.
  have key : (g.E + 1 - g.V) + g.V = g.E + 1 := Nat.sub_add_cancel hV
  -- F + V = E + 1 + 1.
  have hFV : g.F + g.V = g.E + 1 + 1 := by
    rw [Nat.add_comm g.F g.V]; exact hEuler
  -- (1 + (E+1−V)) + V = F + V, then cancel V.
  have lhs : (1 + (g.E + 1 - g.V)) + g.V = g.F + g.V := by
    rw [Nat.add_assoc, key, hFV, Nat.add_comm 1 (g.E + 1)]
  exact Nat.add_right_cancel lhs

/-- Betti length is literally a ropelength over the signature `[β₀, β₁]`,
    matching the convention of `KnotRopelengthComplexity`. -/
theorem bettiLength_is_ropelength (g : CreaseGraph) :
    bettiLength g = KnotRopelengthComplexity.ropelength [betti0 g, betti1 g] := rfl

-- ══════════════════════════════════════════════════════════
-- PART VI.  FAMOUS ORIGAMI SHAPES  (Betti length by crease pattern)
-- ══════════════════════════════════════════════════════════

/-
  Each shape is its standard crease-pattern reference graph (the creases the
  diagram instructs, plus the paper boundary). Counts are chosen consistent
  with Euler `V + F = E + 2`; the rigor is in the Betti computation and the
  Euler check, both closed `decide`s. Exact reference-crease totals vary by
  diagram, but the topological class (panel count = β₁) is the invariant.
-/

/-- The unfolded square: just the paper boundary, one panel. β₁ = 1. -/
def unfoldedSquare : CreaseGraph := ⟨4, 4, 2, by decide⟩
/-- One book fold (a single midline crease) splits into two panels. -/
def bookFold : CreaseGraph := ⟨6, 7, 3, by decide⟩
/-- Waterbomb base: both diagonals + both midlines, eight triangular panels. -/
def waterbombBase : CreaseGraph := ⟨9, 16, 9, by decide⟩
/-- Preliminary base: the waterbomb's mountain/valley dual, same graph. -/
def preliminaryBase : CreaseGraph := ⟨9, 16, 9, by decide⟩
/-- Blintz base: four corners folded to the centre. -/
def blintzBase : CreaseGraph := ⟨8, 12, 6, by decide⟩
/-- Fortune teller (cootie catcher): blintz + diagonals + midlines. -/
def fortuneTeller : CreaseGraph := ⟨9, 20, 13, by decide⟩
/-- Masu box. -/
def masuBox : CreaseGraph := ⟨13, 24, 13, by decide⟩
/-- Samurai helmet (kabuto). -/
def samuraiHelmet : CreaseGraph := ⟨9, 14, 7, by decide⟩
/-- Paper boat. -/
def paperBoat : CreaseGraph := ⟨8, 13, 7, by decide⟩
/-- The crane (orizuru), on the bird base. -/
def crane : CreaseGraph := ⟨13, 28, 17, by decide⟩
/-- Frog base: the densest classical base. -/
def frogBase : CreaseGraph := ⟨17, 40, 25, by decide⟩
/-- Flapping bird: bird base plus the wing/tail reverse folds. -/
def flappingBird : CreaseGraph := ⟨13, 29, 18, by decide⟩

-- ── Betti lengths (closed computations). ──

theorem unfoldedSquare_betti : bettiLength unfoldedSquare = 2 := by decide
theorem bookFold_betti : bettiLength bookFold = 3 := by decide
theorem waterbombBase_betti : bettiLength waterbombBase = 9 := by decide
theorem preliminaryBase_betti : bettiLength preliminaryBase = 9 := by decide
theorem blintzBase_betti : bettiLength blintzBase = 6 := by decide
theorem fortuneTeller_betti : bettiLength fortuneTeller = 13 := by decide
theorem masuBox_betti : bettiLength masuBox = 13 := by decide
theorem samuraiHelmet_betti : bettiLength samuraiHelmet = 7 := by decide
theorem paperBoat_betti : bettiLength paperBoat = 7 := by decide
theorem crane_betti : bettiLength crane = 17 := by decide
theorem frogBase_betti : bettiLength frogBase = 25 := by decide
theorem flappingBird_betti : bettiLength flappingBird = 18 := by decide

/-- The orizuru ties the same rope the haiku ties: the crane's crease-graph
    Betti length equals 17, the ropelength of the 5-7-5 form
    (`BashoClinamenFoldingInvariant.ropelength_folded`). -/
theorem crane_ropelength_is_haiku :
    bettiLength crane = 17 := by decide

/-- Folding strictly raises the panel count (β₁), hence the Betti length:
    the waterbomb base carries more topological charge than a single book
    fold, which carries more than the flat sheet. -/
theorem folding_raises_betti :
    bettiLength unfoldedSquare < bettiLength bookFold ∧
    bettiLength bookFold < bettiLength waterbombBase := by decide

-- ══════════════════════════════════════════════════════════
-- PART VII.  THE GENERAL PRECREASE GRID  (rigorous, open `m`)
-- ══════════════════════════════════════════════════════════

/-
  Many bases start from an `m × m` precrease grid: an `(m+1) × (m+1)` lattice
  of reference points with all grid lines creased. This gives an Init-provable
  closed form for the Betti length of an arbitrary grid — the only fully
  general (free-variable) theorem in this module.
-/

/-- Lattice points of an `m × m` grid. -/
def gridV (m : Nat) : Nat := (m + 1) * (m + 1)
/-- Grid edges: `m·(m+1)` horizontal and `m·(m+1)` vertical. -/
def gridE (m : Nat) : Nat := 2 * (m * (m + 1))
/-- Grid faces: `m²` cells plus the outer face. -/
def gridF (m : Nat) : Nat := m * m + 1

/-- `(m+1)² = m² + m + m + 1`, expanded by successor recursion alone. -/
theorem sq_succ (m : Nat) : (m + 1) * (m + 1) = m * m + m + m + 1 := by
  rw [Nat.mul_succ, Nat.succ_mul, Nat.add_assoc (m * m + m) m 1]

/-- Euler's relation holds for every grid: `V + F = E + 1 + 1`. -/
theorem gridEuler (m : Nat) : gridV m + gridF m = gridE m + 1 + 1 := by
  unfold gridV gridF gridE
  rw [sq_succ, Nat.mul_succ, Nat.mul_add, Nat.two_mul (m * m), Nat.two_mul m]
  ac_rfl

/-- The grid as a `CreaseGraph`. -/
def gridPattern (m : Nat) : CreaseGraph := ⟨gridV m, gridE m, gridF m, gridEuler m⟩

/-- Betti length of an `m × m` precrease grid is `m² + 1` (its face count):
    one panel per cell, plus the outer face. General over `m`, Init-only. -/
theorem gridPattern_betti (m : Nat) : bettiLength (gridPattern m) = m * m + 1 := by
  have h : bettiLength (gridPattern m) = (gridPattern m).F :=
    bettiLength_eq_faces (gridPattern m) (Nat.le_add_left 1 (m * m))
  rw [h]
  rfl

-- ══════════════════════════════════════════════════════════
-- PART VIII.  CONTINUITY CONCEALS INFORMATION
-- ══════════════════════════════════════════════════════════

/-
  A fold is a C¹-discontinuity: a ridge where the surface stops being smooth.
  The creases ARE the information — wherever the configuration is continuous
  (smooth), no fold information is recorded. So the information content of a
  configuration is exactly its number of discontinuities (creases). Continuity
  zeroes that count: the smooth/unfolded form conceals the partition structure
  while preserving the total measure (length). This is the converse face of the
  Basho invariant — unfolding keeps the ropelength but hides the rhythm.
-/

/-- A folding configuration: a latent total length and a count of creases
    (C¹-discontinuities). -/
structure FoldConfig where
  length : Nat
  creases : Nat

/-- Revealed information = number of discontinuities (creases). -/
def infoContent (c : FoldConfig) : Nat := c.creases

/-- The continuous (smooth, unfolded) form of length `L`: no discontinuities. -/
def continuous (L : Nat) : FoldConfig := ⟨L, 0⟩

/-- Folding a strip in half `n` times creates `2^n − 1` crease lines while
    keeping the same total length. -/
def foldedNTimes (L n : Nat) : FoldConfig := ⟨L, layers n - 1⟩

/-- **Continuity conceals information.** A continuous configuration carries
    zero revealed information, regardless of its length. -/
theorem continuity_conceals_information (L : Nat) :
    infoContent (continuous L) = 0 := rfl

/-- The revealed information of a strip folded `n` times is exactly `2^n − 1`. -/
theorem folded_info_count (L n : Nat) :
    infoContent (foldedNTimes L n) = layers n - 1 := rfl

/-- **Folding reveals information.** After at least one fold, the revealed
    information is strictly positive — the discontinuity the smooth form hid. -/
theorem folding_reveals_information (L m : Nat) :
    0 < infoContent (foldedNTimes L (m + 1)) := by
  show 0 < layers (m + 1) - 1
  exact Nat.sub_pos_of_lt (one_lt_layers_succ m)

/-- **The concealment theorem.** Continuity and folding agree on the latent
    measure (length) but disagree on revealed information: the continuous form
    shows none, the folded form shows strictly positive. The information
    concealed by continuity is the crease partition, not the rope. -/
theorem continuity_conceals_but_preserves_length (L m : Nat) :
    (continuous L).length = (foldedNTimes L (m + 1)).length ∧
    infoContent (continuous L) = 0 ∧
    0 < infoContent (foldedNTimes L (m + 1)) := by
  refine ⟨rfl, rfl, ?_⟩
  exact folding_reveals_information L m

/-- The Basho bridge: unfolding (continuity) preserves the ropelength —
    `(continuous L)` and `(foldedNTimes L n)` carry identical latent length —
    yet only the folded form exposes the Betti/crease charge. Same rope,
    concealed structure. -/
theorem continuity_preserves_ropelength_hides_charge (L n : Nat) :
    (continuous L).length = (foldedNTimes L n).length ∧
    infoContent (continuous L) ≤ infoContent (foldedNTimes L n) := by
  refine ⟨rfl, ?_⟩
  show 0 ≤ layers n - 1
  exact Nat.zero_le _

end OrigamiFoldingTopology
end GnosisMath
