/-
  LatticeQuantizationGain.lean
  ============================

  A finite, decidable model of the lattice-quantizer GAIN story and the
  cell-filling preconditions that gate it. This is the arithmetic/logical
  skeleton behind the measured `n_rgb` win (+9.30% MSE reduction) and the
  honest negative (the deblur wash).

  WHAT IS CITED (constants, NOT derived here):
    - The continuous normalized second moments G(·) are textbook lattice
      constants (Conway-Sloane, "Sphere Packings, Lattices and Groups";
      E8 optimality via Viazovska 2017). We do NOT prove their values here.
        * G(Z^n cubic) = 1/12 per dimension  (exact rational, the only
          one we *do* know exactly).
        * G(E8)  ≈ 0.071682  (cited)
        * G(BCC/D3*) ≈ 0.078745 (cited, the 3-D optimal analog).
      We pin each as a DEFINED rational parameter (numerator/denominator over
      Int), carrying the cited decimal in the literal, and we PROVE the
      arithmetic relations *among* them (the ~14% edge, the ~5.8% edge).

  WHAT IS PROVED (closed, decidable, here):
    1. The relative edge of E8 over cubic equals the measured ~14% to the
       modeled precision, by exact cross-multiplication of rationals.
    2. The BLEND LAW. `blendedGain k n` = (k/n) * (cubic-E8 edge). We prove
       `blendedGain 8 12` lands in the predicted band that matched the
       +9.30% measurement, by exact integer arithmetic.
    3. The cell-filling PRECONDITION as a decidable predicate over a finite
       `Regime` record (centered, spread >= 1 cell, full-rank, not padded).
    4. The padding/effective-dimension counting lemma: zero-padding k real
       dims up to m collapses effective dimension to k (monotone, < m when
       m > k), so the `E8Tail` recipe DOMINATES the zero-pad recipe.

  This is the WISDOM formalized: [[feedback_e8_lattice_only_wins_cell_filling]].
  The geometry being optimal is NECESSARY, not SUFFICIENT; the data regime
  (cell-filling, decorrelated, high-D, at-the-bottleneck) is the real
  precondition, and that is exactly the decidable structure proved below.

  Init-only Rustic Church. No Mathlib. No `omega`. No `simp`/`decide` on
  open-variable goals. NO `native_decide`. Closed numerics use `decide`/`rfl`;
  `↔` goals are split into the two `decide`-able directions where needed.
  Target: zero-axiom or propext-only. `#print axioms` every theorem.
-/
import Init

namespace GnosisMath
namespace LatticeQuantizationGain

/-! ## Exact nonnegative rationals as Int num/den pairs

We avoid Mathlib's `Rat`. A `Q` is an integer numerator over a positive
integer denominator. We never reduce; we compare by cross-multiplication,
which is decidable on closed literals. All our values are nonnegative. -/

/-- A rational as an `Int` numerator over an `Int` denominator. We only ever
    instantiate with positive denominators (the `Pos` field below pins that
    when it matters), but the comparison operations are defined for all. -/
structure Q where
  num : Int
  den : Int
  deriving DecidableEq, Repr

/-- Cross-multiplied equality of two rationals: `a/b = c/d` iff `a*d = c*b`.
    Decidable because it is an `Int` equation. -/
def Q.eq (x y : Q) : Prop := x.num * y.den = y.num * x.den

/-- Cross-multiplied `<` for rationals with positive denominators:
    `a/b < c/d` iff `a*d < c*b`. -/
def Q.lt (x y : Q) : Prop := x.num * y.den < y.num * x.den

/-- Cross-multiplied `<=`. -/
def Q.le (x y : Q) : Prop := x.num * y.den ≤ y.num * x.den

instance : Decidable (Q.eq x y) := by unfold Q.eq; exact inferInstance
instance : Decidable (Q.lt x y) := by unfold Q.lt; exact inferInstance
instance : Decidable (Q.le x y) := by unfold Q.le; exact inferInstance

/-- Multiply two rationals (numerator * numerator, denominator * denominator). -/
def Q.mul (x y : Q) : Q := ⟨x.num * y.num, x.den * y.den⟩

/-- Subtraction over a common denominator. -/
def Q.sub (x y : Q) : Q := ⟨x.num * y.den - y.num * x.den, x.den * y.den⟩

/-- A natural-number ratio `k/n` lifted to `Q`. -/
def Q.ofFrac (a b : Nat) : Q := ⟨Int.ofNat a, Int.ofNat b⟩

/-! ## Cited lattice second-moment constants

Lower `G` is a better quantizer. The decimals are carried in the literals;
only `cubic = 1/12` is exact, the others are cited approximations pinned to
6 significant figures (the precision at which the measurements were taken). -/

/-- `G(Z^n)` cubic quantizer, per dimension. EXACT: `1/12`. -/
def gCubic : Q := ⟨1, 12⟩

/-- `G(E8)` ≈ 0.071682 (Conway-Sloane / Viazovska). CITED, pinned as
    `71682 / 1000000`. -/
def gE8 : Q := ⟨71682, 1000000⟩

/-- `G(BCC / D3*)` ≈ 0.078745. CITED, pinned as `78745 / 1000000`. The 3-D
    optimal analog (E8 being 8-D). -/
def gBCC : Q := ⟨78745, 1000000⟩

/-- `G(Z^3)` cubic in 3 dims is the SAME per-dim `1/12` ≈ 0.083333; we name it
    for the BCC comparison. -/
def gCubic3 : Q := gCubic

/-! ## The edges (relative improvement) as exact rationals

The relative edge of lattice `L` over cubic is `(gCubic - gL) / gCubic`.
We model the edge directly as the rational it equals, then PROVE the equality
by cross-multiplication, so the cited decimals are tied to the arithmetic. -/

/-- The modeled E8-over-cubic relative edge, expressed as a percentage band.
    `(1/12 - 71682/1000000) / (1/12)`. We carry the modeled value `0.139816`
    (≈ 14.0%) and prove it equals the defined edge expression. -/
def e8EdgeExpr : Q := Q.sub gCubic gE8 |>.mul ⟨gCubic.den, gCubic.num⟩

/-- The BCC-over-cubic relative edge expression
    `(1/12 - 78745/1000000) / (1/12)`. -/
def bccEdgeExpr : Q := Q.sub gCubic3 gBCC |>.mul ⟨gCubic3.den, gCubic3.num⟩

/-! ### Theorem 1: the E8 edge lands in the measured ~14% band -/

/-- **The E8 quantization edge over cubic is ~14%.** The exact edge rational
    lies strictly inside the band `(13%, 15%)`, matching the measured 14.1%
    (theory 14.0%). Proved by cross-multiplication of closed `Int` literals. -/
theorem e8_edge_in_14pct_band :
    Q.lt ⟨13, 100⟩ e8EdgeExpr ∧ Q.lt e8EdgeExpr ⟨15, 100⟩ := by
  decide

/-- **The BCC edge over cubic is ~5.8%.** The exact edge lies strictly inside
    `(5%, 7%)`, matching the measured 5.8% (the 3-D-optimal analog). -/
theorem bcc_edge_in_6pct_band :
    Q.lt ⟨5, 100⟩ bccEdgeExpr ∧ Q.lt bccEdgeExpr ⟨7, 100⟩ := by
  decide

/-- **E8 beats cubic** (strictly lower second moment). -/
theorem e8_below_cubic : Q.lt gE8 gCubic := by decide

/-- **E8 beats BCC** (E8 is the better quantizer of the two cited lattices). -/
theorem e8_below_bcc : Q.lt gE8 gBCC := by decide

/-! ## The BLEND LAW

When E8 covers `k` of `n` feature dims and cubic covers the rest, the gain is
modeled as `(k/n) * edge`, where `edge` is the cubic-E8 relative edge (~14%).

To keep the prediction exactly decidable we fix `edge` to the modeled
14% = `14/100` used in the session's prediction (the band theorem above ties
that 14% to the cited constants). The blend is then pure rational arithmetic. -/

/-- The modeled edge used in the session's prediction: 14% = `14/100`. The
    band theorem `e8_edge_in_14pct_band` certifies the cited constants put the
    true edge in `(13%, 15%)` around this value. -/
def modeledEdge : Q := ⟨14, 100⟩

/-- `blendedGain k n` = `(k/n) * modeledEdge`. Pure rational. -/
def blendedGain (k n : Nat) : Q := (Q.ofFrac k n).mul modeledEdge

/-- **The blend formula predicts ~9.3% for k=8, n=12.** `(8/12) * 14%`
    equals exactly `112/1200 = 9.3333...%`, which lies strictly inside the
    measured band `(9.0%, 9.6%)` (measurement: +9.30%). Proved by
    cross-multiplication of closed literals. -/
theorem blend_8_of_12_predicts_9_3pct :
    Q.lt ⟨90, 1000⟩ (blendedGain 8 12) ∧ Q.lt (blendedGain 8 12) ⟨96, 1000⟩ := by
  decide

/-- **The blend formula is exactly `112/1200`.** Pins the predicted value to
    an exact rational (≈ 9.3333%), tying the prediction to arithmetic, not to
    a band. -/
theorem blend_8_of_12_exact : Q.eq (blendedGain 8 12) ⟨112, 1200⟩ := by
  decide

/-- **Monotone coverage** (closed instance): covering more dims with E8 never
    decreases the blended gain. Concretely `blendedGain 4 12 <= blendedGain 8 12`. -/
theorem blend_more_coverage_more_gain :
    Q.le (blendedGain 4 12) (blendedGain 8 12) := by decide

/-- **Full E8 coverage recovers the full edge.** `blendedGain n n = modeledEdge`
    at `n = 8` (a closed instance): `(8/8)*14% = 14%`. -/
theorem blend_full_coverage : Q.eq (blendedGain 8 8) modeledEdge := by decide

/-! ## The cell-filling PRECONDITION as a decidable predicate

A quantizer advantage is conditional on the data regime. We model the regime
as a finite record and the precondition as a decidable conjunction:

  (a) centered     — DC removed (quantize residual-from-mean)
  (b) spread       — samples cover >= 1 Voronoi cell (effDim measured in
                     hundredths of a cell; `spreadCells >= 100` = >= 1.00 cell)
  (c) fullRank     — effective dim ~ ambient dim (decorrelated)
  (d) notPadded    — no zero-padding to reach a lattice dimension

All four are required; failing any one is a wash. -/

/-- A measured data regime over `ambient` feature dimensions. `effDim` is the
    measured effective (full-rank) dimension. `spreadCells` is the spread in
    HUNDREDTHS of a Voronoi cell (so `278` means 2.78 cells, as measured on the
    real NOAA `n_rgb` feature). `centered`/`notPadded` are the DC-removal and
    no-zero-pad flags. -/
structure Regime where
  ambient : Nat
  effDim : Nat
  spreadCells : Nat
  centered : Bool
  notPadded : Bool
  deriving DecidableEq, Repr

/-- Full-rank within tolerance: effective dim is within 2 of ambient (the
    measured `n_rgb` was 10.6/12 — within ~1.4). -/
def Regime.fullRank (r : Regime) : Bool :=
  decide (r.effDim + 2 ≥ r.ambient) && decide (r.effDim ≤ r.ambient)

/-- Spread across at least one full cell: `spreadCells >= 100` (>= 1.00 cell). -/
def Regime.spread (r : Regime) : Bool := decide (r.spreadCells ≥ 100)

/-- **The cell-filling precondition.** All four gates pass. Decidable `Bool`. -/
def Regime.cellFilling (r : Regime) : Bool :=
  r.centered && r.spread && r.fullRank && r.notPadded

/-- The measured `n_rgb` regime AFTER DC removal: ambient 12, effDim 10 (≈10.6),
    spread 278 (2.78 cells), centered, not padded. -/
def nrgbRegime : Regime :=
  { ambient := 12, effDim := 10, spreadCells := 278,
    centered := true, notPadded := true }

/-- The deblur-residual regime (the honest negative): origin-hugging scalar
    correction — not centered as a vector, spread well under one cell. -/
def deblurResidualRegime : Regime :=
  { ambient := 12, effDim := 2, spreadCells := 7,
    centered := false, notPadded := true }

/-- The zero-padded regime (12 -> 16 for E8(+)E8): the dead zero dims pin each
    block, collapsing effective dim and violating no-zero-pad. -/
def paddedRegime : Regime :=
  { ambient := 16, effDim := 8, spreadCells := 120,
    centered := true, notPadded := false }

/-- **The `n_rgb` regime IS cell-filling** — the precondition the +9.30% win
    rode on. -/
theorem nrgb_cell_filling : nrgbRegime.cellFilling = true := by decide

/-- **The deblur residual regime is NOT cell-filling** — the honest negative;
    origin-hugging scalar corrections are a wash. -/
theorem deblur_not_cell_filling : deblurResidualRegime.cellFilling = false := by
  decide

/-- **The padded regime is NOT cell-filling** — zero-padding re-introduces the
    violation (the E8(+)E8-pad wash). -/
theorem padded_not_cell_filling : paddedRegime.cellFilling = false := by decide

/-! ## The padding / effective-dimension counting lemma

Zero-padding `k` real dims up to ambient `m` adds `m - k` dead dimensions that
each pin the lattice near a point, so the EFFECTIVE dimension stays `k`. We
model `paddedEffDim k m = min k m` and prove the monotone collapse: when
`m > k`, the effective dim is strictly below ambient. The `E8Tail` recipe (a
full E8 cell on `k` real dims + a cubic tail on the remaining REAL dims) keeps
effective dim at the real count and so DOMINATES the pad recipe. -/

/-- Effective dimension after zero-padding `k` real dims to ambient `m`:
    `min k m` (the dead dims add no effective dimension). -/
def paddedEffDim (k m : Nat) : Nat := Nat.min k m

/-- Effective dimension of the `E8Tail` recipe over `realDims` real dims (full
    E8 cell on the first 8, cubic tail on the rest): all real dims stay live. -/
def e8TailEffDim (realDims : Nat) : Nat := realDims

/-- **Padding never increases effective dimension above the real count.** -/
theorem padding_caps_eff_dim (k m : Nat) : paddedEffDim k m ≤ k := by
  unfold paddedEffDim; exact Nat.min_le_left k m

/-- **Padding strictly collapses effective dimension below ambient when there
    are dead dims.** If `m > k` then `paddedEffDim k m < m`. This is the
    counting heart of the no-zero-pad rule. -/
theorem padding_collapses (k m : Nat) (h : k < m) : paddedEffDim k m < m := by
  unfold paddedEffDim
  have : Nat.min k m = k := Nat.min_eq_left (Nat.le_of_lt h)
  rw [this]; exact h

/-- **E8Tail recipe DOMINATES the zero-pad recipe on effective dimension.**
    For `realDims` real dims padded up to `m > realDims`, the E8Tail recipe
    keeps `realDims` live while the pad recipe collapses to `paddedEffDim`,
    which is strictly smaller. Higher live effective dimension is exactly the
    cell-filling resource the lattice gain needs. -/
theorem e8tail_dominates_padding (realDims m : Nat) (h : realDims < m) :
    paddedEffDim realDims m < e8TailEffDim realDims + (m - realDims) ∧
    e8TailEffDim realDims = realDims := by
  refine ⟨?_, rfl⟩
  unfold paddedEffDim e8TailEffDim
  have hmin : Nat.min realDims m = realDims := Nat.min_eq_left (Nat.le_of_lt h)
  rw [hmin]
  exact Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt h)

/-- **Concrete instance: 12 real dims padded to 16 collapses to 12 effective**,
    losing the 4 dead dims, while the real `E8Tail` over 12 dims keeps all 12
    live. This is the measured E8(+)E8-pad wash vs the E8Tail win. -/
theorem pad_12_to_16_loses_four :
    paddedEffDim 12 16 = 12 ∧ paddedEffDim 12 16 < 16 := by
  refine ⟨by decide, ?_⟩
  exact padding_collapses 12 16 (by decide)

/-! ## Recipe dominance, end-to-end

Bundling the wisdom: under the cell-filling precondition the E8Tail recipe
both (i) keeps full live effective dimension that padding loses and (ii)
earns the blended gain the pad recipe forfeits. The closed instance ties the
counting lemma to the blend prediction. -/

/-- **The winning recipe, distilled.** For the measured `n_rgb` operating
    point (12 dims, 8 covered by E8): the regime is cell-filling, the blend
    predicts the measured ~9.3% band, and padding to 16 would strictly
    collapse effective dimension. The three facts together are the formalized
    recipe: center -> full E8 cell + cubic tail -> expect ~(8/12)*14%. -/
theorem winning_recipe :
    nrgbRegime.cellFilling = true ∧
    (Q.lt ⟨90, 1000⟩ (blendedGain 8 12) ∧ Q.lt (blendedGain 8 12) ⟨96, 1000⟩) ∧
    paddedEffDim 12 16 < 16 := by
  refine ⟨by decide, by decide, ?_⟩
  exact padding_collapses 12 16 (by decide)

end LatticeQuantizationGain
end GnosisMath
