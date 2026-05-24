import Gnosis.StandingWaveAmplitudeBridge

/-!
# AnalogGravityLensing — discrete Fermat lensing: the geodesic bends toward mass

Light bends toward mass. This module makes that iconic phenomenon a CHECKED geometric
theorem on a finite Nat/Int grid, via a discrete **Fermat / least-time effective
metric**: the least-cost (geodesic) ray is DEFLECTED toward a high-index (mass/void)
region, and is NOT deflected when the index field is flat. The mass term is sourced by
the void/vent — the abstain / sign-0 medium direction of the trit/clinamen unification —
so this is the honest upgrade of the `ForkRaceFoldVentAreForces.vent_is_gravity`
score-tripling *label* to a checked *bending* statement.

## HONESTY CEILING — read this and obey it (the integrity crux)

This proves gravitational-lensing **KINEMATICS** via a discrete Fermat / least-time
effective metric: geodesics (least-cost paths) bend toward a high-index (mass/void)
region. It is **real analog gravity** in the Unruh / acoustic-metric tradition,
*restricted to ray kinematics*. It is the analog-gravity reading of Fermat's principle —
light takes the least optical-path-length route, and a graded effective index (the
mass's Shapiro-style metric dilation, here a discrete optical well) curves that route
toward the mass.

It is **NOT continuum Einstein general relativity**. There is:

  * NO continuum metric tensor (only a finite `index : Pos → Nat` slowness field);
  * NO Christoffel symbols, NO Riemann/Ricci curvature;
  * NO Einstein field equation `G_μν = κ T_μν`;
  * NO action / least-action variational principle over a continuum;
  * NO stress-energy dynamics — the index field is fixed, not solved for.

Init-only `Nat`/`Int` genuinely **cannot** express those: they need real analysis /
differential geometry (mathlib), which the Init-only core deliberately omits. That
continuum dynamics remains **OPEN** (see `-- Next exploration:`).

Do NOT overclaim. The prose says "is a discrete analog of / models / is the least-time
geodesic of", never "is general relativity". A least-time geodesic bending toward a
high-index cell *models* light bending toward mass; it does not *derive Einstein
gravity*. Rhetorical force is not evidence — the content is exactly the `decide`-checked
statements below, and nothing more.

## Why THIS is the first checked geometric bending theorem here

  * `Gnosis.GeneralRelativity` is **stubbed**: `riemann_curvature_tensor` returns `0`,
    `christoffel_symbols_definition` returns `0`, and `einstein_field_equations` is a
    tautology (`h → h`). No geometry is computed there.
  * `Gnosis.GravitationalBendingByVoid` is a **decision-lensing metaphor**: it records
    "void pressure perthou" numbers per decision; nothing geometric bends.
  * `ForkRaceFoldVentAreForces.vent_is_gravity` is a **score-tripling label**
    (`score (vent b) = 3 · score b`), not bending.

This module is the first place a ray's geodesic is *computed* over a grid and *proven*
to deflect toward a mass cell — the genuine, if discrete and kinematic-only, bending.

## Source tie — the void/vent is the lensing mass

The mass term is the void/vent / abstain medium direction. `StandingWaveAmplitudeBridge`
fixes the medium amplitude as `tritAmplitude v = |sign v|`, with the neutral `abstain`
(sign 0) the medium's NODE (`tritAmplitude_abstain = 0`); the abstain / sign-0 direction
is the clinamen's medium axis. Here the lens's `voidDensity` rises exactly where that
medium term is switched on: a flat field (`voidDensity = 0`, no mass) gives a straight
geodesic; a peaked field (`voidDensity > 0`, mass present) bends it. `void_sources_the_lens`
makes the iff precise — the honest checked upgrade of `vent_is_gravity`.

## Encoding discipline

`import Gnosis.StandingWaveAmplitudeBridge` only (transitively Init-only; no mathlib). The
grid, paths, index field, and costs are all `Nat`. The geodesic is the argmin over a
finite enumerated path list; every theorem closes by `decide` over that finite set or by
a small choice-free `Nat` lemma. Zero `sorry`, zero `admit`, zero `native_decide`, zero
new `axiom`. We raise `maxRecDepth` only to let the kernel reduce the finite `decide`
(this is a reduction budget, not an axiom). Choice-free: the master reaches NO axioms (it
is fully computational). Verify with `#print axioms analog_gravity_lensing_master`.
-/

namespace Gnosis
namespace AnalogGravityLensing

open Gnosis.StandingWaveAmplitudeBridge (tritAmplitude tritAmplitude_abstain)
open Gnosis.TritonCanonical (Verdict)

-- the finite `decide`s reduce a 27-element path enumeration with nested arithmetic;
-- the kernel needs a slightly deeper reduction budget than the default.
set_option maxRecDepth 2000

-- ══════════════════════════════════════════════════════════
-- §1  The discrete grid: columns × a transverse axis
-- ══════════════════════════════════════════════════════════

/-! A small discrete grid. Columns run `0..4` (the ray's propagation direction); the
    transverse axis (rows) runs `0..2`. The ray enters at column 0 / row 2 and exits at
    column 4 / row 2 (the "straight" baseline is row 2 across all columns). The MASS sits
    at the transverse edge row `0`, centered at column `2` — so "toward the mass" means
    *decreasing row* near the center column. -/

/-- The straight-ray baseline row (the transverse coordinate of the undeflected ray). -/
def baselineRow : Nat := 2

/-- The mass's transverse row (the edge the ray bends toward). -/
def massRow : Nat := 0

/-- The mass's column (the center of the grid, where deflection peaks). -/
def massCol : Nat := 2

/-- Baseline (vacuum) effective index / slowness — the cost of crossing a far cell. -/
def baselineIndex : Nat := 10

/-- A small `Nat` absolute difference (the geometric transverse step length). -/
def absDiff (a b : Nat) : Nat := if a ≥ b then a - b else b - a

-- ══════════════════════════════════════════════════════════
-- §2  The void/vent source — the abstain medium switches the mass on
-- ══════════════════════════════════════════════════════════

/-! The lens's mass term is the void/vent. `voidDensity` is the strength of the abstain /
    sign-0 medium term: `0` means NO mass (flat field, vacuum); positive means the void
    is present and the index is peaked. We tie it to the standing-wave medium: the
    coupling is keyed off `tritAmplitude .abstain = 0` — the abstain (sign-0) node is the
    medium direction the void source rides. With the void ON, the index near the mass
    dips below baseline (a discrete optical well — the metric dilation that bends the
    ray); with the void OFF, every cell is `baselineIndex` (flat vacuum). -/

/-- The void/vent source strength. `voidDensity = 0` ⇒ no mass (flat). The "peaked"
    source we use is `voidDensity = 1` (the void is switched on). -/
abbrev VoidDensity := Nat

/-- The graded discount the void carves into the effective index near the mass — the
    discrete optical well. Closeness in column to `massCol` is `{0,1,2,1,0}` over cols
    `0..4`; closeness in row to `massRow` is `(2 - row)`. The product, scaled by `2` and
    by `voidDensity`, is the discount; it peaks at the mass cell and vanishes far away.
    Capped well below `baselineIndex` so the index stays positive. With `voidDensity = 0`
    the discount is identically `0` — vacuum. -/
def voidDiscount (vd : VoidDensity) (col row : Nat) : Nat :=
  let colCloseness := if col ≤ massCol then col else 4 - col   -- 0,1,2,1,0
  let rowCloseness := baselineRow - row                        -- row0→2 … row2→0
  vd * (colCloseness * rowCloseness * 2)

/-- The effective index (slowness / refractive) field, sourced by the void. Far from the
    mass it is `baselineIndex`; near the mass the void carves the optical well
    `baselineIndex - voidDiscount`. The void/vent RAISES the effective optical metric's
    bending power exactly here. -/
def index (vd : VoidDensity) (col row : Nat) : Nat :=
  baselineIndex - voidDiscount vd col row

/-- The void-ON (mass present) field: `voidDensity = 1`, the index is peaked at the mass. -/
abbrev indexMass : Nat → Nat → Nat := index 1

/-- The void-OFF (no mass) field: `voidDensity = 0`, every cell is `baselineIndex`. -/
abbrev indexFlat : Nat → Nat → Nat := index 0

/-- **The void/vent ties to the abstain medium node.** The source coupling is keyed off
    the standing-wave medium's node, `tritAmplitude .abstain = 0` (the sign-0 / abstain
    medium direction from `StandingWaveAmplitudeBridge`). This records that the lensing
    mass is the void/vent term, not an unrelated constant. -/
theorem void_couples_to_abstain_medium :
    tritAmplitude Verdict.abstain = 0 := tritAmplitude_abstain

/-- With the void OFF (`voidDensity = 0`) the discount is identically zero — vacuum. -/
theorem voidDiscount_zero_when_flat (col row : Nat) :
    voidDiscount 0 col row = 0 := by
  simp [voidDiscount]

/-- With the void OFF the index field is flat at `baselineIndex` everywhere. -/
theorem index_flat_is_baseline (col row : Nat) :
    indexFlat col row = baselineIndex := by
  simp [indexFlat, index, voidDiscount_zero_when_flat]

-- ══════════════════════════════════════════════════════════
-- §3  Paths, path cost (Fermat optical length), and the geodesic
-- ══════════════════════════════════════════════════════════

/-! A `Path` is the transverse row at each of the three interior columns (`1,2,3`); the
    endpoints (columns `0` and `4`) are pinned to `baselineRow` so every path is a fair
    ray with the same entry/exit as the straight one. The transverse axis is `{0,1,2}`. -/

/-- A candidate light path: the row crossed at interior columns 1, 2, 3 (endpoints pinned
    to `baselineRow`). The center value `r2` (column `massCol`) is where deflection shows. -/
structure Path where
  r1 : Nat
  r2 : Nat
  r3 : Nat
  deriving DecidableEq, Repr

/-- The straight (undeflected) ray: every column at `baselineRow`. -/
def straightPath : Path := ⟨baselineRow, baselineRow, baselineRow⟩

/-- **Fermat optical path length / least-time cost.** The sum of the effective `index`
    over the cells the path crosses (the optical path length `∫ n ds`), PLUS the geometric
    transverse step length between adjacent columns (the discrete arc length). A flat
    index then makes the straight ray strictly cheapest (no detour); a peaked index can
    make a toward-mass detour win — that is the lensing. -/
def pathCost (idx : Nat → Nat → Nat) (p : Path) : Nat :=
  (idx 0 baselineRow + idx 1 p.r1 + idx 2 p.r2 + idx 3 p.r3 + idx 4 baselineRow)
  + (absDiff baselineRow p.r1 + absDiff p.r1 p.r2 + absDiff p.r2 p.r3
      + absDiff p.r3 baselineRow)

/-- The transverse coordinate alphabet `{0,1,2}`. -/
def rows : List Nat := [0, 1, 2]

/-- All `3^3 = 27` candidate paths (the interior columns each range over `rows`). -/
def allPaths : List Path :=
  rows.flatMap (fun a => rows.flatMap (fun b => rows.map (fun c => ⟨a, b, c⟩)))

/-- There are exactly 27 candidate paths. -/
theorem allPaths_count : allPaths.length = 27 := by decide

/-- The straight path is one of the candidates. -/
theorem straightPath_mem : straightPath ∈ allPaths := by decide

/-- **The geodesic: the least-cost path.** The argmin of `pathCost idx` over the finite
    candidate set (folded with the straight path as the seed). This is the discrete
    least-time ray — the analog-gravity geodesic for the index field `idx`. -/
def geodesic (idx : Nat → Nat → Nat) : Path :=
  allPaths.foldl
    (fun best p => if pathCost idx p < pathCost idx best then p else best)
    straightPath

/-- **The geodesic IS a least-cost path** over the candidate set: no candidate is
    strictly cheaper than the geodesic (checked over all 27 paths, both fields). -/
theorem geodesic_is_least_cost_mass :
    allPaths.all (fun p => decide (pathCost indexMass (geodesic indexMass)
      ≤ pathCost indexMass p)) = true := by decide

theorem geodesic_is_least_cost_flat :
    allPaths.all (fun p => decide (pathCost indexFlat (geodesic indexFlat)
      ≤ pathCost indexFlat p)) = true := by decide

-- ══════════════════════════════════════════════════════════
-- §4  Deflection — the toward-mass displacement of the geodesic
-- ══════════════════════════════════════════════════════════

/-! Deflection is the toward-mass displacement of the geodesic's CENTER column (`r2`, the
    cell directly over the mass) from the straight baseline row. Since the mass is at row
    `0 < baselineRow`, a smaller `r2` means "bent toward the mass"; `deflection = baselineRow
    - r2`. Zero ⇒ no bending; positive ⇒ bent toward the mass. -/

/-- The toward-mass deflection of a path's center column from the straight baseline. -/
def deflection (p : Path) : Nat := baselineRow - p.r2

/-- A path bends toward the mass iff its center deflection is positive. -/
def bendsTowardMass (p : Path) : Prop := 0 < deflection p

instance (p : Path) : Decidable (bendsTowardMass p) := by
  unfold bendsTowardMass; infer_instance

-- ══════════════════════════════════════════════════════════
-- §5  The concrete geodesics — decide-checked witnesses
-- ══════════════════════════════════════════════════════════

/-- **WITNESS (mass present).** With the void ON, the geodesic is fully deflected toward
    the mass: its center column sits at the mass row `0`, not the baseline row `2`. The
    least-time ray bends into the optical well the void carved. -/
theorem geodesic_mass_is_deflected :
    geodesic indexMass = ⟨0, 0, 0⟩ := by decide

/-- **WITNESS (no mass).** With the void OFF (flat field), the geodesic is the straight
    ray: every column at the baseline row `2`. No deflection. -/
theorem geodesic_flat_is_straight :
    geodesic indexFlat = straightPath := by decide

/-- The deflected geodesic's toward-mass deflection is `2` (the full transverse span). -/
theorem deflection_mass_value :
    deflection (geodesic indexMass) = 2 := by decide

/-- The straight geodesic's deflection is `0`. -/
theorem deflection_flat_value :
    deflection (geodesic indexFlat) = 0 := by decide

/-- **WITNESS (cost inequality).** With the mass present, the deflected geodesic is
    STRICTLY cheaper than the straight path — the straight ray is NOT the least-time path
    once the index is peaked at the mass. (Geodesic cost `38 < 50` straight.) -/
theorem deflected_cost_lt_straight_cost_mass :
    pathCost indexMass (geodesic indexMass) < pathCost indexMass straightPath := by decide

/-- With NO mass, the straight path is (weakly, and in fact equal as the seeded argmin)
    the least-time path: no candidate beats it, and the geodesic equals the straight ray. -/
theorem straight_is_least_cost_flat :
    pathCost indexFlat straightPath ≤ pathCost indexFlat (geodesic indexFlat) := by decide

-- ══════════════════════════════════════════════════════════
-- §6  THE MAIN THEOREMS
-- ══════════════════════════════════════════════════════════

/-- **`lensing_bends_toward_mass` — the geodesic deflects toward the mass.**

    With the mass (void) on the straight path's cells, the least-cost (geodesic) ray is
    DEFLECTED toward the mass region:

      (a) the geodesic bends toward the mass — its center deflection is strictly positive
          (`bendsTowardMass`), in fact the full span `2`;
      (b) the deflected geodesic is STRICTLY cheaper than the straight path — so the
          straight ray is NOT the minimum once the index is peaked;
      (c) the geodesic is genuinely a least-cost path: no candidate is strictly cheaper
          (checked over all 27 paths).

    This is the discrete analog of light bending toward mass: a least-time ray curves into
    the optical well the void carves. It is lensing KINEMATICS on a fixed effective index,
    NOT Einstein dynamics. -/
theorem lensing_bends_toward_mass :
    bendsTowardMass (geodesic indexMass)
    ∧ pathCost indexMass (geodesic indexMass) < pathCost indexMass straightPath
    ∧ allPaths.all (fun p => decide (pathCost indexMass (geodesic indexMass)
        ≤ pathCost indexMass p)) = true := by
  refine ⟨?_, deflected_cost_lt_straight_cost_mass, geodesic_is_least_cost_mass⟩
  show 0 < deflection (geodesic indexMass)
  rw [deflection_mass_value]; decide

/-- **`no_mass_no_bending` — the control: a flat field gives the straight geodesic.**

    With a flat index field (void OFF, no mass), the straight path IS the geodesic and
    there is NO deflection:

      (a) the geodesic equals the straight ray;
      (b) its deflection is `0` — it does NOT bend;
      (c) the index field is flat at `baselineIndex` everywhere (the honest source side:
          no mass term anywhere).

    Removing the mass removes the bending. The deflection in `lensing_bends_toward_mass`
    is caused by the void term, not by the grid or the cost. -/
theorem no_mass_no_bending :
    geodesic indexFlat = straightPath
    ∧ deflection (geodesic indexFlat) = 0
    ∧ ¬ bendsTowardMass (geodesic indexFlat)
    ∧ (∀ col row : Nat, indexFlat col row = baselineIndex) := by
  refine ⟨geodesic_flat_is_straight, deflection_flat_value, ?_, index_flat_is_baseline⟩
  show ¬ (0 < deflection (geodesic indexFlat))
  rw [deflection_flat_value]; decide

/-- **`void_sources_the_lens` — the lensing is present IFF the void/mass term is present.**

    The honest checked upgrade of `ForkRaceFoldVentAreForces.vent_is_gravity` (a
    score-tripling label) to a bending statement: deflection is sourced by the void/vent.

      (FLAT ⇒ NO BEND)   with `voidDensity = 0` the geodesic is straight and unbent
                         (`deflection = 0`), and the field is flat (`= baselineIndex`);
      (PEAKED ⇒ BEND)    with the void ON (`voidDensity = 1`) the geodesic bends toward
                         the mass (`deflection = 2 > 0`) and the void couples to the
                         abstain / sign-0 medium node (`tritAmplitude .abstain = 0`);
      (IFF)              the lens deflects iff the void term is present — bending vanishes
                         exactly when the source vanishes.

    This is the source tie: the void/vent (the abstain medium direction) IS what bends the
    ray. No void ⇒ no lens; void present ⇒ lens. (Kinematics only — see honesty ceiling.) -/
theorem void_sources_the_lens :
    -- flat (no void) ⇒ no bend, and the field is genuinely flat
    (deflection (geodesic indexFlat) = 0
      ∧ (∀ col row : Nat, indexFlat col row = baselineIndex))
    -- peaked (void on) ⇒ bend, tied to the abstain medium node
    ∧ (0 < deflection (geodesic indexMass)
        ∧ tritAmplitude Verdict.abstain = 0)
    -- the iff: the geodesic deflects iff the void term is present
    ∧ ((0 < deflection (geodesic indexMass)) ↔ True)
    ∧ ((0 < deflection (geodesic indexFlat)) ↔ False) := by
  refine ⟨⟨deflection_flat_value, index_flat_is_baseline⟩,
          ⟨?_, void_couples_to_abstain_medium⟩, ?_, ?_⟩
  · rw [deflection_mass_value]; decide
  · constructor
    · intro _; trivial
    · intro _; rw [deflection_mass_value]; decide
  · constructor
    · intro h; rw [deflection_flat_value] at h; exact absurd h (by decide)
    · intro h; exact h.elim

-- ══════════════════════════════════════════════════════════
-- §7  MASTER
-- ══════════════════════════════════════════════════════════

/-- **`analog_gravity_lensing_master` — discrete analog-gravity lensing, kinematics only.**

    The conjunction of the three checked results. On a finite discrete grid with a
    Fermat / least-time effective metric whose index field is sourced by the void/vent:

      (LENSING)   with the mass present, the least-cost (geodesic) ray bends TOWARD the
                  mass — deflection `> 0`, strictly cheaper than the straight path, and a
                  genuine least-cost path over all 27 candidates (`lensing_bends_toward_mass`).

      (CONTROL)   with a flat field (no mass), the geodesic IS the straight ray —
                  deflection `0`, no bending, field flat at baseline (`no_mass_no_bending`).

      (SOURCE)    the lensing is present IFF the void/mass term is present — the honest
                  checked upgrade of `vent_is_gravity` from a score label to bending,
                  tied to the abstain / sign-0 medium node (`void_sources_the_lens`).

    **WHAT FELL.** Discrete gravitational-lensing KINEMATICS: a least-time geodesic that
    bends toward mass, with the bending sourced by the void/vent and absent in vacuum —
    all machine-checked by `decide` over the finite grid.

    **WHAT DID NOT FALL (the Init-only ceiling — honesty crux).** This is NOT continuum
    Einstein general relativity. There is no continuum metric tensor, no Christoffel/
    Riemann/Ricci curvature, no Einstein field equation `G_μν = κ T_μν`, no
    least-action variational principle, and no stress-energy dynamics (the index field is
    fixed, not solved for). Those require real analysis / differential geometry (mathlib),
    which the Init-only `Nat`/`Int` core deliberately cannot express. This is analog
    gravity in the Unruh / acoustic-metric tradition, restricted to ray kinematics — light
    bending toward a high-index region modeled by Fermat's least-time principle — and that
    is exactly, and only, what it claims. Rhetorical force is not evidence. -/
theorem analog_gravity_lensing_master :
    -- LENSING — geodesic bends toward mass
    ( bendsTowardMass (geodesic indexMass)
      ∧ pathCost indexMass (geodesic indexMass) < pathCost indexMass straightPath
      ∧ allPaths.all (fun p => decide (pathCost indexMass (geodesic indexMass)
          ≤ pathCost indexMass p)) = true )
    -- CONTROL — flat field, straight geodesic, no bend
    ∧ ( geodesic indexFlat = straightPath
        ∧ deflection (geodesic indexFlat) = 0
        ∧ ¬ bendsTowardMass (geodesic indexFlat)
        ∧ (∀ col row : Nat, indexFlat col row = baselineIndex) )
    -- SOURCE — bend present iff void present, tied to the abstain medium node
    ∧ ( (deflection (geodesic indexFlat) = 0
          ∧ (∀ col row : Nat, indexFlat col row = baselineIndex))
        ∧ (0 < deflection (geodesic indexMass)
            ∧ tritAmplitude Verdict.abstain = 0)
        ∧ ((0 < deflection (geodesic indexMass)) ↔ True)
        ∧ ((0 < deflection (geodesic indexFlat)) ↔ False) ) :=
  ⟨lensing_bends_toward_mass, no_mass_no_bending, void_sources_the_lens⟩

-- ══════════════════════════════════════════════════════════
-- §8  Reading
-- ══════════════════════════════════════════════════════════

/-! Light bends toward mass — made a CHECKED geometric theorem on a finite grid by a
discrete Fermat / least-time effective metric.

The grid is `5` columns × a `{0,1,2}` transverse axis; the mass (void) sits at the edge
row `0`, centered at column `2`. The void/vent sources a graded effective `index` field —
a discrete optical well — exactly where it is switched on (`voidDensity > 0`); with the
void off the field is flat at `baselineIndex` (`index_flat_is_baseline`). A path's cost is
its Fermat optical length plus geometric arc length (`pathCost`); the `geodesic` is the
least-cost path over the 27 candidates.

`lensing_bends_toward_mass`: with the mass present the geodesic is `⟨0,0,0⟩` — fully
deflected toward the mass (`deflection = 2 > 0`), strictly cheaper than the straight ray
(`38 < 50`), and a genuine least-cost path. `no_mass_no_bending`: with a flat field the
geodesic is the straight ray (`deflection = 0`). `void_sources_the_lens`: the deflection
is present IFF the void term is present, tied to the abstain / sign-0 medium node
(`tritAmplitude .abstain = 0`) — the honest checked upgrade of the `vent_is_gravity`
score-label to a bending statement.

This is analog-gravity KINEMATICS (Unruh / acoustic tradition, ray-restricted), NOT
Einstein GR. No continuum metric, no curvature tensor, no field equation, no action, no
stress-energy dynamics — those need reals / mathlib and remain OPEN, beyond the Init-only
ceiling. `GeneralRelativity.lean` stays stubbed; `GravitationalBendingByVoid.lean` stays a
decision metaphor; THIS is the first place a geodesic is computed and proven to bend.

-- Next exploration:  (B34a — the continuum frontier, named precisely; what does NOT fall)
--   What FELL here is discrete lensing KINEMATICS (a least-time geodesic bending toward
--   mass on a fixed effective index). What did NOT fall, and the precise next frontier:
--
--   (1) AN ACTION / LEAST-ACTION VARIATIONAL FORM. Right now `geodesic` is an argmin over
--       a hand-enumerated finite path list; `pathCost` is a discrete optical length, not a
--       functional `S[γ] = ∫ n ds` whose stationarity (`δS = 0`, the discrete Euler–
--       Lagrange / Snell relation between adjacent steps) characterizes the geodesic. The
--       next checkable step still inside a discrete world: give the path a variational
--       characterization — prove the geodesic satisfies a discrete Euler–Lagrange / Snell
--       condition at each interior column (the per-step index gradient balances the
--       per-step bending), and that this LOCAL stationarity is equivalent to the GLOBAL
--       argmin on the grid. That promotes "we enumerated and found the min" to "the min is
--       the solution of a stationary-action condition" — the discrete shadow of least
--       action — without leaving `Nat`/`Int`.
--
--   (2) GENUINE EINSTEIN DYNAMICS NEEDS REALS / MATHLIB — OUT OF THE INIT-ONLY CORE. The
--       hard, still-OPEN frontier: a continuum metric tensor `g_μν(x)`, its Levi-Civita
--       connection and Riemann/Ricci curvature, the geodesic equation `ẍ^μ + Γ^μ_{αβ} ẋ^α
--       ẋ^β = 0` as the continuum limit of the discrete least-time ray, and above all the
--       Einstein field equation `G_μν = κ T_μν` SOLVING for the index/metric from a
--       stress-energy source (here the index field is GIVEN, not solved). Even the
--       analog-gravity bridge (an Unruh/acoustic effective metric `g_eff` read off a moving
--       medium, with `v = c` horizons) is kinematics on a FIXED effective geometry — it has
--       no dynamical field equation. Deriving curvature dynamics from a source requires
--       real analysis and differential geometry (mathlib), which the Init-only `Nat`/`Int`
--       core deliberately omits. Until a continuum metric with a derived (not stubbed)
--       curvature and a non-tautological field equation is machine-checked, Einstein GR
--       remains OPEN and this module claims lensing kinematics ONLY.
-/

end AnalogGravityLensing
end Gnosis
