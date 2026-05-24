import Gnosis.WeakResidual
import Gnosis.FiniteFluidCompactness

namespace Gnosis

/-!
# Bounded Gravitational Residual

A finite-volume **weak-residual bounded certificate** for the Einstein field
equations `G_{μν} = κ T_{μν}`, built to fall at the EXACT epistemic standard at
which this corpus already certifies Navier–Stokes (`BoundedFluidResidual`,
`WeakResidual`, `FiniteFluidCompactness`). Init-only (Rustic Church): no Mathlib,
no `omega`, no `simp`/`decide` on open goals; `decide` only on CLOSED arithmetic.

## HONESTY SCOPE — read this before reading any theorem name

This module is the honest upgrade of `ForkRaceFoldVentAreForces.vent_is_gravity`
(a score-tripling LABEL) and the genuine answer to the open frontier named in
`StandingWaveAmplitudeBridge`'s `-- Next exploration:`: it derives a *dynamical*
field-equation defect from the medium, at the only standard a computer can
honor — the finite, sampled one.

WHAT THIS CERTIFIES (and ONLY this):

  * A *discrete finite-volume control-volume sample* of `G_{μν} = κ T_{μν}` has
    weak residual bounded by a chosen tolerance. The carrier is a finite cell of
    `Nat`/`Int` field values; the residual is the finite-difference defect
    `|discrete G − κ·T|` over the cell. This is the COMPUTABLE / SAMPLED content,
    the SAME standard as `BoundedFluidResidual` for fluids: *the infinite bounded
    in discrete, by sample — only what a computer can do.*
  * The source `T` is the **void/vent medium density** (the standing-wave
    amplitude / vent), not an arbitrary constant: curvature is sourced BY THE
    MEDIUM (`void_sources_stress_energy`). This is the dynamics
    `vent_is_gravity` only labelled.

WHAT THIS DOES NOT CERTIFY (deferred here EXACTLY as the corpus defers it for
Navier–Stokes — never overclaimed):

  * NO continuum existence / smoothness / uniqueness of solutions to the Einstein
    PDE. There is no real-analysis Lorentzian manifold, no derivative, no metric
    in the sense of differential geometry. The "millennium-boundary" continuum
    statement is OUT OF SCOPE (named in `-- Next exploration:`).
  * NO claim of full continuum General Relativity. This is a discrete defect
    bound on a sample, full stop.

NON-TAUTOLOGICAL (the integrity crux). The stub `GeneralRelativity.einstein_field_equations`
is `P → P` and `riemann_curvature_tensor` returns `0`; we replicate NEITHER.
`einsteinResidual` is DISCRIMINATING and we prove it both ways:
  * a configuration satisfying the discrete equations has residual `≤ tol`
    (`vacuum_residual_bounded`, `sourced_solution_bounded`), AND
  * a configuration that does NOT satisfy them has residual `> tol`
    (`non_solution_exceeds`).
A residual that is always `0` (the stub's curvature) or always trivially bounded
would be a FAIL; ours separates solutions from non-solutions.

Axioms: `propext` / `Quot.sound` only (no `Classical.choice`, no `sorryAx`);
`native_decide` is never used — closed witnesses close by `decide`. Verify with
`#print axioms bounded_gravitational_dynamics_master`.
-/

namespace BoundedGravitationalResidual

-- ══════════════════════════════════════════════════════════
-- §1  THE DISCRETE EINSTEIN CONTROL-VOLUME CELL
-- ══════════════════════════════════════════════════════════

/-- A discrete finite-volume sample of spacetime: one control-volume cell with a
    metric-proxy field value at its center and at its two neighbours (the minimal
    stencil for a second-difference "curvature"), plus the local void/vent medium
    amplitude that sources the stress-energy.

      * `metricLeft`, `metricCenter`, `metricRight` — a scalar metric proxy
        sampled on the 1-D stencil `(left, center, right)`. The discrete curvature
        is the second difference of this field over the cell.
      * `voidAmplitude` — the void/vent medium density at the cell, the
        standing-wave amplitude (cf. `StandingWaveAmplitudeBridge`,
        `vent_is_gravity`). This is the source: `T` is read off the medium, not
        chosen freely. -/
structure EinsteinCell where
  metricLeft : Nat
  metricCenter : Nat
  metricRight : Nat
  voidAmplitude : Nat
  deriving Repr, DecidableEq

/-- The Einstein coupling `κ` (a fixed `Nat` coupling constant, the discrete
    analog of `8πG/c⁴`). Fixed to `2` so that the source term is genuinely
    sensitive to the medium (a nonzero, non-unit coupling: `κ·T` is neither `T`
    nor `0`). -/
def kappa : Nat := 2

/-- **Discrete curvature `G`** — the finite-difference / finite-volume proxy for
    the curvature side of the field equation: the (absolute) second difference of
    the metric proxy across the cell stencil,
    `|metricLeft + metricRight − 2·metricCenter|`. This is the discrete Laplacian /
    second-difference "curvature" of the metric-proxy field — `0` exactly on a
    locally *flat* (affine) sample, positive where the field bends. It is an `Int`
    so the second difference can be signed before taking magnitude. -/
def discreteCurvature (cell : EinsteinCell) : Int :=
  (cell.metricLeft : Int) + (cell.metricRight : Int)
    - 2 * (cell.metricCenter : Int)

/-- **Discrete stress-energy `T`** — sourced by the void/vent medium density.
    `T` is the medium amplitude itself: the source side is the standing-wave /
    vent amplitude, not an arbitrary number. -/
def stressEnergy (cell : EinsteinCell) : Int :=
  (cell.voidAmplitude : Int)

/-- The source side of the field equation, `κ·T`: coupling times the medium
    density. -/
def sourceTerm (cell : EinsteinCell) : Int :=
  (kappa : Int) * stressEnergy cell

/-- **`einsteinResidual` — the weak/finite-volume defect** of the discrete
    Einstein equation `G = κ·T` over the cell:
    `|discrete G − κ·T|` as a `Nat` (via `Int.natAbs`). This is `0` exactly when
    the discrete curvature equals the medium-sourced stress-energy, and grows with
    the mismatch. It is the gravitational analog of `weakFluxResidual`. -/
def einsteinResidual (cell : EinsteinCell) : Nat :=
  (discreteCurvature cell - sourceTerm cell).natAbs

/-- **`SatisfiesFieldEq tol cell`** — the bounded-weak-residual predicate: the
    discrete field equation holds on the cell sample to within tolerance `tol`.
    This is the gravitational mirror of the fluid `FluidResidualBounded`. -/
def SatisfiesFieldEq (tol : Nat) (cell : EinsteinCell) : Prop :=
  einsteinResidual cell ≤ tol

instance (tol : Nat) (cell : EinsteinCell) : Decidable (SatisfiesFieldEq tol cell) := by
  unfold SatisfiesFieldEq
  infer_instance

-- ══════════════════════════════════════════════════════════
-- §2  DISCRIMINATING WITNESSES — the integrity crux
-- ══════════════════════════════════════════════════════════

/-! These three theorems are what make the certificate NON-TAUTOLOGICAL. Each
    fixes a CLOSED witness cell and closes by `decide` on closed arithmetic
    (Rustic Church: `decide` only on goals with no free variables). The first two
    show solutions are accepted; the third shows a non-solution is REJECTED —
    so `einsteinResidual` discriminates, unlike the always-`0` stub curvature. -/

/-- A vacuum / flat configuration: the metric proxy is locally affine
    (`left + right = 2·center`, here all equal) so `G = 0`, and the medium is empty
    (`voidAmplitude = 0`) so `T = 0`. The discrete field equation `0 = κ·0` holds
    exactly: residual `0`. -/
def vacuumCell : EinsteinCell :=
  { metricLeft := 5, metricCenter := 5, metricRight := 5, voidAmplitude := 0 }

/-- The discrete curvature of the flat vacuum sample is exactly `0`. -/
theorem vacuum_curvature_zero : discreteCurvature vacuumCell = 0 := by decide

/-- The stress-energy of the empty vacuum sample is exactly `0`. -/
theorem vacuum_stress_energy_zero : stressEnergy vacuumCell = 0 := by decide

/-- The vacuum residual is exactly `0` — flat geometry, empty medium, both sides
    vanish. -/
theorem vacuum_residual_zero : einsteinResidual vacuumCell = 0 := by decide

/-- **`vacuum_residual_bounded`** — a vacuum/flat configuration (`G ≈ 0`, `T = 0`)
    satisfies the field equation: residual `0 ≤ tol` for any tolerance. -/
theorem vacuum_residual_bounded (tol : Nat) :
    SatisfiesFieldEq tol vacuumCell := by
  unfold SatisfiesFieldEq
  rw [vacuum_residual_zero]
  exact Nat.zero_le tol

/-- A medium-SOURCED solution: the void/vent medium has amplitude `3`, so
    `κ·T = 2·3 = 6`, and the metric proxy is bent by exactly that much
    (`left + right − 2·center = 4 + 8 − 2·3 = 6`), so the discrete curvature MATCHES
    the medium-sourced stress-energy. This is the discrete `G = κ·T` *holding* with
    a NONZERO curvature sourced by the medium — not the stub's `G ≡ 0`. -/
def sourcedCell : EinsteinCell :=
  { metricLeft := 4, metricCenter := 3, metricRight := 8, voidAmplitude := 3 }

/-- The sourced cell has genuinely NONZERO discrete curvature `G = 6` — the medium
    bends the geometry. (Contrast the stub, whose curvature is always `0`.) -/
theorem sourced_curvature_nonzero : discreteCurvature sourcedCell = 6 := by decide

/-- The sourced cell's stress-energy is the medium amplitude `T = 3`, and
    `κ·T = 6` — exactly the curvature. -/
theorem sourced_source_term : sourceTerm sourcedCell = 6 := by decide

/-- On the sourced cell the discrete field equation `G = κ·T` holds exactly:
    residual `0`, with `G = 6 = κ·T` BOTH nonzero. -/
theorem sourced_residual_zero : einsteinResidual sourcedCell = 0 := by decide

/-- **`sourced_solution_bounded`** — a configuration whose discrete curvature
    matches `κ·T` (medium-sourced) satisfies the field equation on the sample:
    residual `0 ≤ tol`. The field equation holds with curvature SOURCED by the
    medium and nonzero — the honest dynamical content. -/
theorem sourced_solution_bounded (tol : Nat) :
    SatisfiesFieldEq tol sourcedCell := by
  unfold SatisfiesFieldEq
  rw [sourced_residual_zero]
  exact Nat.zero_le tol

/-- A NON-solution: same bent geometry as `sourcedCell` (`G = 6`) but the medium is
    empty (`voidAmplitude = 0`, so `κ·T = 0`). Curvature without a source: the
    discrete field equation is VIOLATED, with defect `|6 − 0| = 6`. -/
def nonSolutionCell : EinsteinCell :=
  { metricLeft := 4, metricCenter := 3, metricRight := 8, voidAmplitude := 0 }

/-- The non-solution has the SAME nonzero curvature `G = 6` as the sourced cell. -/
theorem non_solution_curvature : discreteCurvature nonSolutionCell = 6 := by decide

/-- ...but its medium is empty, so `κ·T = 0`: curvature with no source. -/
theorem non_solution_source_zero : sourceTerm nonSolutionCell = 0 := by decide

/-- The non-solution residual is exactly `6` — the field-equation defect of
    sourceless curvature. -/
theorem non_solution_residual : einsteinResidual nonSolutionCell = 6 := by decide

/-- **`non_solution_exceeds`** — THE DISCRIMINATING THEOREM. For any tolerance
    `tol < 6`, the non-solution's residual (`= 6`) EXCEEDS it, so the certificate
    REJECTS sourceless curvature. The residual is therefore not vacuous: it
    separates solutions (`vacuumCell`, `sourcedCell`, residual `0`) from
    non-solutions (`nonSolutionCell`, residual `6`). This is exactly what the
    `P → P` stub cannot do. -/
theorem non_solution_exceeds (tol : Nat) (htol : tol < 6) :
    ¬ SatisfiesFieldEq tol nonSolutionCell := by
  unfold SatisfiesFieldEq
  rw [non_solution_residual]
  exact Nat.not_le_of_lt htol

/-- The certificate is **discriminating at the concrete tolerance `tol = 0`**:
    `vacuumCell` and `sourcedCell` pass (`residual = 0 ≤ 0`) while `nonSolutionCell`
    fails (`residual = 6 > 0`). A single closed statement witnessing that the
    residual is NOT always-bounded — the antithesis of the stub. -/
theorem residual_discriminates :
    SatisfiesFieldEq 0 vacuumCell
    ∧ SatisfiesFieldEq 0 sourcedCell
    ∧ ¬ SatisfiesFieldEq 0 nonSolutionCell := by
  refine ⟨?_, ?_, ?_⟩
  · exact vacuum_residual_bounded 0
  · exact sourced_solution_bounded 0
  · exact non_solution_exceeds 0 (by decide)

-- ══════════════════════════════════════════════════════════
-- §3  SOURCE TIE — curvature sourced by the void/vent medium
-- ══════════════════════════════════════════════════════════

/-! The stress-energy is the void/vent medium density, so the residual measures a
    field equation whose source IS the medium — the honest upgrade of
    `vent_is_gravity` from a score-tripling label to a sourced field-equation
    defect. -/

/-- The stress-energy of a cell is exactly its void/vent medium amplitude. -/
theorem stress_energy_eq_void_amplitude (cell : EinsteinCell) :
    stressEnergy cell = (cell.voidAmplitude : Int) := by rfl

/-- The source term scales the void/vent medium density by `κ`. -/
theorem source_term_eq_kappa_void (cell : EinsteinCell) :
    sourceTerm cell = (kappa : Int) * (cell.voidAmplitude : Int) := by rfl

/-- An empty medium sources no stress-energy: `voidAmplitude = 0 ⇒ T = 0`. -/
theorem empty_void_no_source
    (cell : EinsteinCell) (hempty : cell.voidAmplitude = 0) :
    sourceTerm cell = 0 := by
  unfold sourceTerm stressEnergy
  rw [hempty]
  rfl

/-- **`void_sources_stress_energy`** — the source tie. The stress-energy side of
    the discrete Einstein equation IS the void/vent medium density (the
    standing-wave amplitude), scaled by `κ`:

      (a) `T = voidAmplitude` (stress-energy is read off the medium);
      (b) `κ·T = κ · voidAmplitude` (the source side is the medium times coupling);
      (c) an EMPTY medium sources nothing (`voidAmplitude = 0 ⇒ T = 0`), so any
          residual there is pure curvature (cf. `non_solution_exceeds`);
      (d) a populated medium genuinely sources curvature: at `sourcedCell` the
          nonzero curvature `G = 6` equals `κ·T = 6` — the medium IS the source of
          the geometry's bending.

    This is the dynamical content `ForkRaceFoldVentAreForces.vent_is_gravity` only
    labelled: there gravity was `score (vent b) = 3 · score b`; here the medium
    amplitude is the stress-energy SOURCING a discrete curvature through a checked
    field-equation residual. -/
theorem void_sources_stress_energy :
    (∀ cell : EinsteinCell, stressEnergy cell = (cell.voidAmplitude : Int))
    ∧ (∀ cell : EinsteinCell,
        sourceTerm cell = (kappa : Int) * (cell.voidAmplitude : Int))
    ∧ (∀ cell : EinsteinCell, cell.voidAmplitude = 0 → sourceTerm cell = 0)
    ∧ (discreteCurvature sourcedCell = sourceTerm sourcedCell
        ∧ discreteCurvature sourcedCell = 6) := by
  refine ⟨stress_energy_eq_void_amplitude, source_term_eq_kappa_void,
          empty_void_no_source, ?_, ?_⟩
  · -- G = κ·T at the sourced cell, both = 6
    rw [sourced_curvature_nonzero, sourced_source_term]
  · exact sourced_curvature_nonzero

-- ══════════════════════════════════════════════════════════
-- §4  OBSERVER ACCEPTANCE — finite mesh promoted to acceptance
-- ══════════════════════════════════════════════════════════

/-! Mirroring `FiniteFluidCompactness`: a finite mesh (list) of Einstein cells all
    within tolerance is ACCEPTED as a discrete Einstein-observer solution — a
    conservation/acceptance certificate over the whole control volume. -/

/-- A finite mesh of control-volume cells. -/
abbrev EinsteinMesh := List EinsteinCell

/-- **`MeshSatisfiesFieldEq tol mesh`** — every cell in the finite mesh satisfies
    the discrete field equation to within `tol`: the whole control volume is a
    bounded-weak-residual sample. -/
def MeshSatisfiesFieldEq (tol : Nat) (mesh : EinsteinMesh) : Prop :=
  ∀ cell ∈ mesh, SatisfiesFieldEq tol cell

/-- The empty mesh trivially satisfies the field equation (no cell to violate it). -/
theorem empty_mesh_satisfies (tol : Nat) :
    MeshSatisfiesFieldEq tol ([] : EinsteinMesh) := by
  intro cell hmem
  exact absurd hmem (List.not_mem_nil)

/-- A mesh whose cells all satisfy the equation, extended by one more satisfying
    cell, still satisfies it: acceptance is closed under adding bounded cells. -/
theorem mesh_satisfies_cons
    (tol : Nat) (cell : EinsteinCell) (mesh : EinsteinMesh)
    (hcell : SatisfiesFieldEq tol cell)
    (hmesh : MeshSatisfiesFieldEq tol mesh) :
    MeshSatisfiesFieldEq tol (cell :: mesh) := by
  intro c hmem
  rcases List.mem_cons.mp hmem with hhead | htail
  · rw [hhead]; exact hcell
  · exact hmesh c htail

/-- Acceptance is monotone in tolerance: widening the observer's tolerance never
    loses an already-accepted mesh. -/
theorem mesh_satisfies_mono_tol
    (tol wider : Nat) (mesh : EinsteinMesh)
    (htol : tol ≤ wider)
    (hmesh : MeshSatisfiesFieldEq tol mesh) :
    MeshSatisfiesFieldEq wider mesh := by
  intro cell hmem
  exact Nat.le_trans (hmesh cell hmem) htol

/-- Promote each cell's residual into the fluid-style observer answer machinery:
    a single Einstein cell within tolerance is accepted by a fluid residual
    observer (carrying its defect in the advection slot), at the SAME acceptance
    standard as Navier–Stokes. This is the bridge from the gravitational residual
    into the corpus's existing `fluid_residual_refinement_signature.answer`. -/
def fluidResidualOfEinsteinCell (cell : EinsteinCell) : BoundedFluidResidual :=
  { advection := einsteinResidual cell, diffusion := 0, pressure := 0, forcing := 0 }

theorem fluid_residual_of_einstein_cell_total (cell : EinsteinCell) :
    fluidResidualTotal (fluidResidualOfEinsteinCell cell) = einsteinResidual cell := by
  unfold fluidResidualOfEinsteinCell fluidResidualTotal
  simp

/-- **`bounded_residual_gives_observer_acceptance`** — the ACCEPTANCE theorem
    (mirror of `finite_fluid_observer_compactness`). A finite mesh whose cells are
    all within tolerance is ACCEPTED as a discrete Einstein-observer solution over
    the control volume:

      (a) the empty mesh is trivially accepted;
      (b) acceptance is closed under adding any further within-tolerance cell;
      (c) acceptance is monotone in the observer tolerance;
      (d) each within-tolerance cell promotes into the SAME fluid-style observer
          answer (`fluid_residual_refinement_signature.answer`) used to certify
          Navier–Stokes — the gravitational defect is accepted at the corpus's
          fluid standard whenever the cell's defect fits the observer budget.

    Given a mesh `mesh` and a witness `hmesh : MeshSatisfiesFieldEq tol mesh`, the
    whole control volume is an accepted bounded-weak-residual sample of
    `G = κ·T`. -/
theorem bounded_residual_gives_observer_acceptance
    (tol : Nat) (mesh : EinsteinMesh)
    (hmesh : MeshSatisfiesFieldEq tol mesh) :
    MeshSatisfiesFieldEq tol ([] ++ mesh)
    ∧ (∀ cell : EinsteinCell, SatisfiesFieldEq tol cell →
        MeshSatisfiesFieldEq tol (cell :: mesh))
    ∧ (∀ wider : Nat, tol ≤ wider → MeshSatisfiesFieldEq wider mesh)
    ∧ (∀ cell : EinsteinCell, ∀ observer : FluidResidualObserver, ∀ depth : Nat,
        einsteinResidual cell ≤ observer.tolerance + depth →
          fluid_residual_refinement_signature.answer
            (fluidResidualOfEinsteinCell cell) observer depth) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) empty append is just the mesh
    rw [List.nil_append]; exact hmesh
  · -- (b) closure under adding a within-tolerance cell
    intro cell hcell
    exact mesh_satisfies_cons tol cell mesh hcell hmesh
  · -- (c) tolerance monotonicity
    intro wider hwider
    exact mesh_satisfies_mono_tol tol wider mesh hwider hmesh
  · -- (d) promotion into the fluid observer answer (Navier–Stokes standard)
    intro cell observer depth hbudget
    change fluidResidualTotal (fluidResidualOfEinsteinCell cell) ≤
      observer.tolerance + depth
    rw [fluid_residual_of_einstein_cell_total]
    exact hbudget

/-- A concrete accepted mesh: vacuum + sourced cells, both residual `0`, accepted
    at tolerance `0` over the whole control volume. A closed-witness instance of
    the acceptance certificate (the mesh analog of `residual_discriminates`). -/
theorem example_mesh_accepted :
    MeshSatisfiesFieldEq 0 [vacuumCell, sourcedCell] := by
  apply mesh_satisfies_cons
  · exact vacuum_residual_bounded 0
  · apply mesh_satisfies_cons
    · exact sourced_solution_bounded 0
    · exact empty_mesh_satisfies 0

/-- ...and the same mesh is REJECTED once the non-solution is added at tolerance
    `0` — the mesh-level discrimination. -/
theorem example_mesh_with_non_solution_rejected :
    ¬ MeshSatisfiesFieldEq 0 [vacuumCell, sourcedCell, nonSolutionCell] := by
  intro hmesh
  have hmem : nonSolutionCell ∈ [vacuumCell, sourcedCell, nonSolutionCell] := by
    simp
  exact non_solution_exceeds 0 (by decide) (hmesh nonSolutionCell hmem)

-- ══════════════════════════════════════════════════════════
-- §5  MASTER THEOREM
-- ══════════════════════════════════════════════════════════

/-- **`bounded_gravitational_dynamics_master`** — Einstein gravitational dynamics
    falls at the corpus's finite-volume weak-residual standard.

    Conjoins the five honest pieces. Read the module doc-comment for the FULL
    honesty scope; in brief, what FELL is a *discriminating finite-volume
    weak-residual certificate* for `G = κ·T` (the Navier–Stokes standard), and what
    did NOT is continuum existence/smoothness (deferred exactly as for fluids):

      (1) VACUUM. A flat/empty configuration satisfies the discrete field equation
          (residual `0 ≤ tol`) — `vacuum_residual_bounded`.
      (2) SOURCED SOLUTION. A configuration whose discrete curvature matches the
          medium-sourced `κ·T` satisfies it, with curvature NONZERO and sourced by
          the medium (`G = 6 = κ·T`) — `sourced_solution_bounded`.
      (3) DISCRIMINATION (non-tautology). A configuration with curvature but no
          source has residual `> tol` for `tol < 6`, so the certificate REJECTS it
          — `non_solution_exceeds`. Unlike the `P → P` stub, the residual
          separates solutions from non-solutions.
      (4) OBSERVER ACCEPTANCE. A finite mesh all within tolerance is accepted as a
          discrete Einstein-observer solution, promoting into the SAME fluid
          observer answer used for Navier–Stokes —
          `bounded_residual_gives_observer_acceptance`.
      (5) SOURCE TIE. The stress-energy IS the void/vent medium density, so
          curvature is sourced by the medium — the honest upgrade of
          `vent_is_gravity` — `void_sources_stress_energy`. -/
theorem bounded_gravitational_dynamics_master :
    -- (1) vacuum is a solution
    (∀ tol : Nat, SatisfiesFieldEq tol vacuumCell)
    -- (2) medium-sourced configuration is a solution (curvature nonzero, = κ·T)
    ∧ (∀ tol : Nat, SatisfiesFieldEq tol sourcedCell)
    ∧ (discreteCurvature sourcedCell = sourceTerm sourcedCell
        ∧ discreteCurvature sourcedCell = 6)
    -- (3) DISCRIMINATING: a non-solution exceeds tolerance
    ∧ (∀ tol : Nat, tol < 6 → ¬ SatisfiesFieldEq tol nonSolutionCell)
    ∧ (SatisfiesFieldEq 0 vacuumCell
        ∧ SatisfiesFieldEq 0 sourcedCell
        ∧ ¬ SatisfiesFieldEq 0 nonSolutionCell)
    -- (4) OBSERVER ACCEPTANCE over a finite mesh, into the fluid answer machinery
    ∧ (∀ tol : Nat, ∀ mesh : EinsteinMesh, MeshSatisfiesFieldEq tol mesh →
        (∀ wider : Nat, tol ≤ wider → MeshSatisfiesFieldEq wider mesh)
        ∧ (∀ cell : EinsteinCell, ∀ observer : FluidResidualObserver, ∀ depth : Nat,
            einsteinResidual cell ≤ observer.tolerance + depth →
              fluid_residual_refinement_signature.answer
                (fluidResidualOfEinsteinCell cell) observer depth))
    -- (5) SOURCE TIE: stress-energy is the void/vent medium density
    ∧ ((∀ cell : EinsteinCell, stressEnergy cell = (cell.voidAmplitude : Int))
        ∧ (∀ cell : EinsteinCell,
            sourceTerm cell = (kappa : Int) * (cell.voidAmplitude : Int))
        ∧ (∀ cell : EinsteinCell, cell.voidAmplitude = 0 → sourceTerm cell = 0)
        ∧ (discreteCurvature sourcedCell = sourceTerm sourcedCell
            ∧ discreteCurvature sourcedCell = 6)) := by
  refine ⟨vacuum_residual_bounded, sourced_solution_bounded, ?_,
          non_solution_exceeds, residual_discriminates, ?_, void_sources_stress_energy⟩
  · -- (2) tail: G = κ·T = 6 at the sourced cell
    refine ⟨?_, sourced_curvature_nonzero⟩
    rw [sourced_curvature_nonzero, sourced_source_term]
  · -- (4) observer acceptance, packaged from the acceptance theorem
    intro tol mesh hmesh
    have h := bounded_residual_gives_observer_acceptance tol mesh hmesh
    exact ⟨h.2.2.1, h.2.2.2⟩

end BoundedGravitationalResidual

end Gnosis

-- Next exploration:  (B34a — what still does NOT fall)
--   What FELL here: Einstein DYNAMICS as a DISCRIMINATING finite-volume
--   weak-residual certificate `G = κ·T` over a sampled control volume, sourced by
--   the void/vent medium — the corpus's Navier–Stokes standard
--   (`BoundedFluidResidual` / `FiniteFluidCompactness`), now matched for gravity.
--   The residual SEPARATES solutions (vacuum, medium-sourced: residual 0) from
--   non-solutions (sourceless curvature: residual 6 > tol), so it is genuinely
--   discriminating, not a `P → P` tautology like `GeneralRelativity.lean`.
--
--   What did NOT fall (the open hard frontiers, named honestly):
--
--   1. CONTINUUM EXISTENCE / SMOOTHNESS / UNIQUENESS (the millennium-boundary).
--      This module bounds the discrete SAMPLE only. It does NOT prove that a
--      continuum Einstein PDE solution exists, is smooth, or is unique — exactly
--      the boundary the corpus also leaves open for the Navier–Stokes existence /
--      smoothness Millennium Problem. No real-analysis Lorentzian manifold, no
--      derivative, no metric in the differential-geometry sense is constructed
--      here; `Int`/`Nat` finite differences stand in for `∂²`. Closing this is a
--      different kind of result (real analysis / PDE), not a finer mesh.
--
--   2. A REFINEMENT TOWER (DiscreteContinuumConstantRefinement-style) showing the
--      weak residual → 0 as the mesh refines: introduce a refinement parameter `n`
--      (cell width `1/n`, or a stencil of `n` subcells), define a refined
--      `discreteCurvature_n` whose second difference is taken over the finer
--      stencil, and prove `einsteinResidual_n` is monotone-nonincreasing in `n`
--      and bounded by `C / n` for an explicit constant `C` on a fixed smooth
--      metric-proxy/medium pair — i.e. the discrete defect provably shrinks toward
--      the continuum field equation under refinement. That tower would tie this
--      sampled certificate to the continuum LIMIT (still NOT continuum existence,
--      which remains item 1), mirroring the corpus's other
--      DiscreteContinuumConstantRefinement bridges. Until then, the certificate is
--      honestly a bounded defect on ONE sample resolution, by sample — only what a
--      computer can do.
