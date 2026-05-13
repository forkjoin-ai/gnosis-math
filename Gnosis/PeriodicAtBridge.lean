import Init

/-!
# Periodic table and atomic scale (Rustic Church boundary)

Formal boundary anchor inside the math library. The **discrete / information-theoretic**
carrier algebra for the IUPAC band is what closes without extra axioms; **SI-colored
numerical identities** (digits tied to meters, electronvolts, CODATA tables) only
enter once you assume a **`PeriodicCalibrationMorphism`** (or richer bridge package).
That split keeps honest which sentences are kernel consequences and which are
calibration hypotheses—not a claim that structure stops being physically meaningful.

See **`Gnosis.PeriodicTableTheoremMatrix`** for the 118×ledger-ID row packaging
(same structural-hole cluster per Z, Mendeleev-eka flags, and the extension band
**Z > 118** with no rows).

## Kernel-side facts (discrete / finite)

These are the usual formal targets in this package, not a new periodic grid.

* **Lattice holes and complement weights** — mechanized in `Gnosis.NonEmpiricalPrediction`
  (`StructuralHole`, `mendeleev_is_complement`, …) and NEI in `Gnosis.NovelInferenceForms`
  (`nei_mendeleev`). Ledger strings remain indexed from `open-source/gnosis/THEOREM_LEDGER.md`.
* **Phase walls** — fermion encoding at Dodecagon score `12`, vacuum at `0`:
  `Gnosis.FermionExclusionEquilibria`, `Gnosis.BosonSkyrmsEquilibria`.
* **Mass ladder as encoding** — `Gnosis.MassHierarchyFromBule` ties scores in `Nat`
  to the narrative (“Pauli tax”): arithmetic identities, not measured mass ratios.
* **Hadronic score witnesses** — internal collision bookkeeping:
  `Gnosis.CompositeParticles`.
* **Standing-wave and mesh routing metaphor** — structural strings and pinning:
  `Gnosis.CosmologicalGuitarString`, `Gnosis.MeshStandingWavePinning`.
* **Discrete Bloch-shaped bookkeeping** — `Gnosis.Materials.BlochTheorem` (toy
  lattice phases, not a laboratory crystal Hamiltonian).

## Bridge layer (explicit Init-only shapes)

Mapping atomic number to a standing-wave index, attaching Bohr-length meters,
reading nuclear decay off a kernel invariant, or identifying Planck–proton gaps
with tower steps—all require **named bridge assumptions** or a calibration
morphism. The types below **name** those obligation slots without importing
`ℝ`, measures, or CODATA tables. Until fields are instantiated with witnessed
maps, those links are **not** consequences of the finite algebra alone.

## Out of scope for direct Init-only formalization

Continuous radii in meters, MeV masses, hydrogen spectra, QCD binding, and
full-field orbitals use **ℝ**, **measure**, or **transcendental** layers that
this kernel treats like any other continuous bridge: reroute through discrete
witnesses or refuse until an explicit axiom package is added.

## Refusals

* Reflexive equalities on phase counts **do not** imply CODATA mass ratios.
* Integer proton/neutron scores **do not** substitute for binding-energy data
  without a stated SI map.
* Proof-style debt in an encoding file (e.g. `omega` where Rustic Church has
  not yet swept) says nothing about empirical truth—only about tactic cleanup
  backlog.

Parent discipline: the Rustic Church cookbook policy in-repo (Init-only
closures, no opaque arithmetic search on promoted kernels).
-/

namespace Gnosis.PeriodicAtBridge

/-! ## Calibration refusal tags (ledger-aligned strings)

Runtime narrative and `PeriodicTableTheoremMatrix` import these verbatim so the
anti-package stays a single Lean anchor—not duplicated prose.
-/

/-- Canonical refusal strings for SI / continuum overclaim without calibration. -/
def refusalCalibrationStrings : List String :=
  ["PERIODIC-AT-BRIDGE-REFUSE-SI-WITHOUT-CALIBRATION"]

theorem refusal_calibration_nonempty : refusalCalibrationStrings ≠ [] :=
  List.cons_ne_nil "PERIODIC-AT-BRIDGE-REFUSE-SI-WITHOUT-CALIBRATION" []

theorem refusal_calibration_singleton_length : refusalCalibrationStrings.length = 1 := rfl

/-! ## Discrete vs SI shadow carriers (Rustic Church discipline)

Mirrors the intent of `Gnosis.TopologicalBridgeAntiTheorems`: finite certificates
live in one carrier; SI or continuum-backed quantities are typed separately so
they cannot silently unify with Mendeleev ledger algebra.
-/

/-- Discrete-side periodic row: IUPAC **Z = 1 .. 118** band as `Fin 118`. -/
structure DiscretePeriodicCarrier where
  /-- 0-based index; atomic number = `idx.val + 1`. -/
  idx : Fin 118

/-- Shadow carrier for SI / continuum calibration layers (no numeric axioms here). -/
structure SiContinuumCarrierShadow where
  /-- Marker reserved for future morphism witnesses (`ℝ`, CODATA packages, …). -/
  calibrationExpected : Bool := true

/-! ### Explicit calibration morphism (typed bridge hook)

Relative scalar shadows stay in `Nat` so this file stays Init-only. Any equality
to measured constants is **hypothesis-level**: it must be stated over a concrete
`PeriodicCalibrationMorphism` value supplied elsewhere.
-/

/-- Bookkeeping slot for a positive rational shadow `num / den` (den intended nonzero). -/
structure MassRatioShadow where
  num : Nat
  den : Nat

/-- Bundles an SI-side marker with a per-row relative mass-ratio assignment. -/
structure PeriodicCalibrationMorphism where
  siMarker : SiContinuumCarrierShadow
  massRatioShadow : DiscretePeriodicCarrier → MassRatioShadow

/-- Extensionality for morphisms (pointwise agreement on rows). -/
theorem PeriodicCalibrationMorphism.ext {φ ψ : PeriodicCalibrationMorphism}
    (hs : φ.siMarker = ψ.siMarker)
    (hf : ∀ row, φ.massRatioShadow row = ψ.massRatioShadow row) : φ = ψ := by
  cases φ
  cases ψ
  subst hs
  congr 1
  funext row
  exact hf row

/-- Project the typed mass-ratio slot carried by a calibration morphism. -/
def massRatioAt (φ : PeriodicCalibrationMorphism) (row : DiscretePeriodicCarrier) : MassRatioShadow :=
  φ.massRatioShadow row

/-- Atomic numbers carried by `DiscretePeriodicCarrier` stay inside **1 .. 118**. -/
def atomicNumber (row : DiscretePeriodicCarrier) : Nat :=
  row.idx.val + 1

theorem atomicNumber_range (row : DiscretePeriodicCarrier) :
    1 ≤ atomicNumber row ∧ atomicNumber row ≤ 118 :=
  And.intro
    (Nat.succ_le_succ (Nat.zero_le row.idx.val))
    (Nat.succ_le_of_lt row.idx.isLt)

/-- Indexed discipline anchor; mathematics lives in the modules cited above. -/
theorem boundary_discipline_id : (0 : Nat) = 0 := rfl

/-- Bundled boundary witness tying refusal tags to discrete carriers (Init-only). -/
theorem periodic_at_bridge_discipline_master :
    refusalCalibrationStrings ≠ []
    ∧ refusalCalibrationStrings.length = 1
    ∧ (∀ row : DiscretePeriodicCarrier, atomicNumber row ≤ 118)
    ∧ (0 : Nat) = 0 :=
  And.intro refusal_calibration_nonempty
    (And.intro refusal_calibration_singleton_length
      (And.intro (fun row => (atomicNumber_range row).2) boundary_discipline_id))

end Gnosis.PeriodicAtBridge
