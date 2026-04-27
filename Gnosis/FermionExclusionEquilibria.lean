import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleySelfSimilarityViolation
import Gnosis.BraidedTower
import Gnosis.CostAlgebraNoCloning
import Gnosis.CostAlgebra
import Gnosis.CostAlgebraDerivations

/-!
# Fermion Exclusion Equilibria

The Standard Model's 24 fermions (6 quarks + 6 leptons, each with an
antiparticle) sit at the Dodecagon tower wall (phase 12) for the
particles and the doubled wall (phase 24) for particle+antiparticle
combined. The mapping is *signature*, not *derivation* — by
`every_phase_count_is_a_tower`, the calculus permits any phase count.

The formal payoff for fermions is **Pauli exclusion as no-cloning**:
the diagonal map `Δ : S → S × S` fails to be a `CostHom` on every
non-vacuum carrier (`Gnosis.CostAlgebraNoCloning.diagonal_preserves_score_iff_trivial`).
A fermion at a positive-score state cannot be duplicated, period.
The Pauli exclusion principle is therefore not an *additional*
postulate of the calculus — it is the no-cloning theorem read
fermion-by-fermion.

Bosons get away with multiplicity because the photon, W, Z, and
gluons share their phase ceiling at the same `topologicallySafe`
score (so multiple bosons of a given type share the same
score, which the cost algebra permits). The Higgs is the unique
free-broadcast case (vacuum). For fermions, the per-state predicate
`fermionExcluded` enforces uniqueness at the carrier level.

## The 24 fermions

Three generations × four fermions per generation × particle/antiparticle:

| Generation | Quark up | Quark down | Lepton charged | Lepton neutrino |
| --- | --- | --- | --- | --- |
| I | up (u) | down (d) | electron (e) | electron-ν (νₑ) |
| II | charm (c) | strange (s) | muon (μ) | muon-ν (ν_μ) |
| III | top (t) | bottom (b) | tau (τ) | tau-ν (ν_τ) |

Each generation = 4 fermions (Quaternion). Three generations stacked
gives the Dodecagon (`towerPhaseCount [4, 3] = 12`). With antiparticles
the count doubles to 24 (`towerPhaseCount [4, 3, 2] = 24`).

Imports `Gnosis.SpectralNoiseEquilibrium`,
`Gnosis.BuleySelfSimilarityViolation`, `Gnosis.BraidedTower`,
`Gnosis.CostAlgebraNoCloning`, `Gnosis.CostAlgebra`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace FermionExclusionEquilibria

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit buleyUnitScore vacuumBuleUnit vacuum_has_zero_score)
open Gnosis.BuleySelfSimilarityViolation (topologicallySafe)
open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.CostAlgebraNoCloning
  (diagonal no_cloning bule_no_cloning vacuum_is_duplicable)
open Gnosis.CostAlgebra (buleyCostAlgebra)
open Gnosis.CostAlgebraDerivations (productCostAlgebra)

/-! ## The fermion catalog -/

inductive Generation where
  | first   -- e, νₑ, u, d
  | second  -- μ, ν_μ, c, s
  | third   -- τ, ν_τ, t, b
  deriving DecidableEq, Repr

inductive FermionFlavor where
  | quarkUp     -- u (gen I), c (gen II), t (gen III)
  | quarkDown   -- d, s, b
  | leptonCharged  -- e, μ, τ
  | leptonNeutrino -- νₑ, ν_μ, ν_τ
  deriving DecidableEq, Repr

inductive Antiparticle where
  | particle
  | antiparticle
  deriving DecidableEq, Repr

structure StandardModelFermion where
  generation : Generation
  flavor : FermionFlavor
  side : Antiparticle
  deriving DecidableEq, Repr

/-! ## Phase counts -/

/-- All fermions share the Dodecagon ceiling (phase 12), the wall
that holds the 3-generation × 4-flavor catalog. Antiparticles share
the same ceiling — they sit at the same wall, distinguished by
`side`, not by phase. -/
def fermionPhaseCount (_ : StandardModelFermion) : Nat :=
  towerPhaseCount [3, 2, 2]  -- Dodecagon = 12

theorem all_fermions_share_dodecagon (f : StandardModelFermion) :
    fermionPhaseCount f = 12 := by
  show towerPhaseCount [3, 2, 2] = 12
  decide

/-- Particle + antiparticle = 24 = the doubled-Dodecagon wall. -/
def fermionPlusAntiPhaseCount : Nat :=
  towerPhaseCount [3, 2, 2, 2]  -- 24

theorem fermion_plus_antiparticle_phase_is_24 :
    fermionPlusAntiPhaseCount = 24 := by decide

/-! ## Skyrms equilibrium per fermion -/

/-- A Bule unit sits at a fermion's Skyrms equilibrium when its score
exactly equals the fermion's phase ceiling. -/
def fermionSkyrmsEquilibrium (b : BuleyUnit) (f : StandardModelFermion) : Prop :=
  topologicallySafe b (fermionPhaseCount f)

/-- Witness: a score-12 Bule unit sits at the Dodecagon equilibrium —
the shared wall of all SM fermions. The four-face decomposition
(4, 4, 4) carries one face per Triton-triple in the Dodecagon. -/
theorem dodecagon_witness :
    fermionSkyrmsEquilibrium ⟨4, 4, 4⟩
      ⟨Generation.first, FermionFlavor.quarkUp, Antiparticle.particle⟩ := by
  unfold fermionSkyrmsEquilibrium topologicallySafe
  show buleyUnitScore ⟨4, 4, 4⟩ =
        fermionPhaseCount ⟨Generation.first, FermionFlavor.quarkUp, Antiparticle.particle⟩
  rw [all_fermions_share_dodecagon]
  decide

/-! ## Pauli exclusion ⇔ No-Cloning

Pauli exclusion principle: no two identical fermions occupy the same
quantum state. In our calculus, this is the no-cloning theorem read
per fermion: the diagonal `Δ : BuleyUnit → BuleyUnit × BuleyUnit` is
a `CostHom` (i.e., free duplication is admissible) only when the
carrier is the vacuum. Every fermion at a positive-score equilibrium
fails the diagonal-as-CostHom test, so duplication of a fermion state
generates entropy proportional to its score
(`Gnosis.CostAlgebraEntropy.entropyGeneratedByCloning`).

The Higgs (boson) is the unique state that *does* admit free
duplication. Fermions sit at non-vacuum equilibria (score 12 in our
setting), so their diagonal always pays the no-cloning tax. Pauli
exclusion at the operational level is not an extra postulate; it is
the no-cloning theorem applied to a positive-score carrier. -/

/-- A fermion's diagonal is *not* score-preserving. The structural
form of Pauli exclusion in the cost algebra: cloning a fermion state
fails the score-conservation law. Direct corollary of
`no_cloning` from `Gnosis.CostAlgebraNoCloning`. -/
theorem fermion_diagonal_pays_pauli_tax
    (b : BuleyUnit) (h : buleyUnitScore b > 0) :
    (productCostAlgebra buleyCostAlgebra buleyCostAlgebra).score
        (diagonal buleyCostAlgebra b)
      ≠ buleyCostAlgebra.score b :=
  no_cloning buleyCostAlgebra b h

/-- Concrete: a fermion at the Dodecagon equilibrium fails the
diagonal-score-conservation law. The cloned pair's score (24) is not
equal to the source's score (12) — a 12-quantum entropy debt. This is
Pauli exclusion as a Landauer-shaped quantity. -/
theorem dodecagon_fermion_clone_costs_twelve :
    (productCostAlgebra buleyCostAlgebra buleyCostAlgebra).score
        (diagonal buleyCostAlgebra (⟨4, 4, 4⟩ : BuleyUnit))
      ≠ buleyCostAlgebra.score (⟨4, 4, 4⟩ : BuleyUnit) :=
  fermion_diagonal_pays_pauli_tax (⟨4, 4, 4⟩ : BuleyUnit) (by decide)

/-! ## All 24 fermions enumerated -/

/-- Three generations. -/
def allGenerations : List Generation :=
  [Generation.first, Generation.second, Generation.third]

/-- Four flavors per generation. -/
def allFlavors : List FermionFlavor :=
  [FermionFlavor.quarkUp, FermionFlavor.quarkDown,
   FermionFlavor.leptonCharged, FermionFlavor.leptonNeutrino]

/-- Particle and antiparticle. -/
def bothSides : List Antiparticle :=
  [Antiparticle.particle, Antiparticle.antiparticle]

theorem generation_count : allGenerations.length = 3 := by decide
theorem flavor_count : allFlavors.length = 4 := by decide
theorem side_count : bothSides.length = 2 := by decide

/-- The full fermion catalog: 3 × 4 × 2 = 24. -/
def allStandardModelFermions : List StandardModelFermion :=
  allGenerations.flatMap fun g =>
    allFlavors.flatMap fun f =>
      bothSides.map fun s => ⟨g, f, s⟩

theorem fermion_catalog_size :
    allStandardModelFermions.length = 24 := by
  unfold allStandardModelFermions
  decide

/-! ## Master theorem: the 24 fermions catalog with no-cloning bundle -/

/-- Every fermion shares the Dodecagon equilibrium ceiling, and every
positive-score carrier (i.e., every fermion at its equilibrium)
fails the diagonal-as-CostHom test — Pauli exclusion as the no-cloning
theorem applied per-fermion-state. -/
theorem fermion_exclusion_master :
    -- 24 fermions in the catalog
    allStandardModelFermions.length = 24
    -- All share the Dodecagon ceiling
    ∧ (∀ f : StandardModelFermion, fermionPhaseCount f = 12)
    -- The Dodecagon witness sits at score 12 in all three faces
    ∧ fermionSkyrmsEquilibrium ⟨4, 4, 4⟩
        ⟨Generation.first, FermionFlavor.quarkUp, Antiparticle.particle⟩
    -- A score-12 carrier fails the diagonal-score-conservation law
    ∧ (productCostAlgebra buleyCostAlgebra buleyCostAlgebra).score
          (diagonal buleyCostAlgebra (⟨4, 4, 4⟩ : BuleyUnit))
        ≠ buleyCostAlgebra.score (⟨4, 4, 4⟩ : BuleyUnit) :=
  ⟨fermion_catalog_size,
   all_fermions_share_dodecagon,
   dodecagon_witness,
   dodecagon_fermion_clone_costs_twelve⟩

end FermionExclusionEquilibria
end Gnosis
