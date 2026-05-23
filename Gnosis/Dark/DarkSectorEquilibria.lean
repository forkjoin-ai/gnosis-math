import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleySelfSimilarityViolation
import Gnosis.Braided.BraidedTower
import Gnosis.BosonSkyrmsEquilibria
import Gnosis.FermionExclusionEquilibria
import Gnosis.CostAlgebraNoCloning

/-!
# Dark Sector Equilibria

A formal scaffolding for dark-matter and dark-energy candidates as
phase-cycle Skyrms equilibria *between* the canonical Standard-Model
walls. The mapping is *signature*, not *derivation* — by
`every_phase_count_is_a_tower`, the calculus permits arbitrary phase
counts. The dark-sector reading uses the cost-algebra walls that
exist between the SM bosons (Triton 3, Octagon 8) and SM fermions
(Dodecagon 12) but which the SM does not occupy.

## The candidate walls

The Standard-Model phase counts in our calculus are:

- 0 — Higgs / vacuum
- 3 — electroweak bosons (γ, W±, Z⁰) at the Triton
- 8 — gluons at the Octagon
- 12 — fermions at the Dodecagon

The walls *between* and *adjacent* to these are unoccupied by the
SM:

- 4, 5, 6, 7 — between Triton and Octagon
- 9, 10, 11 — between Octagon and Dodecagon

The Hexon (6 = `towerPhaseCount [3, 2]`) is a particularly natural
dark-sector wall — it sits at the *exact midpoint* between the
electroweak Triton and the gluon Octagon, and it has six emanation
slots (matching the six color/anticolor pairs in
`Gnosis.Bosons.Emanation`).

## Two structural readings

### Dark Matter: phase walls between SM walls

A dark-matter candidate is a Bule unit at one of the unoccupied tower
walls (4, 5, 6, 7, 9, 10, 11). These walls don't intersect any SM
phase ceiling, so a dark-matter carrier neither triggers nor
participates in SM governance violations. It gravitates (carries
score) but doesn't interact with SM fields at the SM walls.

### Dark Energy: the vacuum carrier's pervasive reach

The Higgs sits at the vacuum (`vacuumBuleUnit`), and
`vacuum_reaches_any_bule` proves every Bule unit is reached from the
vacuum by `score`-many swerve lifts. The vacuum's *operational
presence* — its role as the source from which every named state
emerges — is structurally dark-energy-like: a uniform background that
doesn't interact directly but is everywhere reachable.

## What this module does *not* claim

- Dark matter / dark energy are real physical entities. (Out of scope.)
- The cost-algebra *forces* dark sectors to exist. (It doesn't —
  this is a structural reading, like the boson signatures.)
- The 6 emanations of `Gnosis.Bosons` are dark matter. (They are
  6/8 of the gluons; they are observed. The Hexon-wall reading here
  is a parallel construction, not the same emanations.)

What this module *does* provide: a named class of phase walls between
SM walls, with a `topologicallySafe` Skyrms-equilibrium witness, and
a non-intersection theorem stating the dark walls don't coincide with
SM walls.

Imports `Gnosis.SpectralNoiseEquilibrium`,
`Gnosis.BuleySelfSimilarityViolation`, `Gnosis.BraidedTower`,
`Gnosis.BosonSkyrmsEquilibria`, `Gnosis.FermionExclusionEquilibria`,
`Gnosis.CostAlgebraNoCloning`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace DarkSectorEquilibria

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit buleyUnitScore vacuumBuleUnit vacuum_has_zero_score
   vacuumToBule vacuum_reaches_any_bule)
open Gnosis.BuleySelfSimilarityViolation (topologicallySafe)
open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.BosonSkyrmsEquilibria (StandardModelBoson bosonPhaseCount)
open Gnosis.FermionExclusionEquilibria
  (StandardModelFermion fermionPhaseCount all_fermions_share_dodecagon)

/-! ## Dark-matter candidate walls -/

inductive DarkSectorParticle where
  /-- The Hexon wall — between Triton (3) and Octagon (8). Six
  emanation slots. -/
  | hexon (i : Fin 6)
  /-- The Pentagon wall (5) — coprime with 3 and not a tower-named
  level for SM. -/
  | pentagon
  /-- The Septagon wall (7) — prime, between Hexon and Octagon. -/
  | septagon
  /-- The Decagon wall (10) — between Octagon and Dodecagon, the
  string-theory dimension signature. -/
  | decagon
  /-- The Hendecagon wall (11) — between Decagon and Dodecagon, the
  M-theory dimension signature. -/
  | hendecagon
  deriving DecidableEq, Repr

/-- The phase ceiling each dark-sector candidate occupies. -/
def darkPhaseCount : DarkSectorParticle → Nat
  | .hexon _ => towerPhaseCount [3, 2]   -- 6
  | .pentagon => 5
  | .septagon => 7
  | .decagon => towerPhaseCount [5, 2]   -- 10
  | .hendecagon => towerPhaseCount [11]  -- 11

theorem dark_phase_counts :
    darkPhaseCount (.hexon 0) = 6
    ∧ darkPhaseCount .pentagon = 5
    ∧ darkPhaseCount .septagon = 7
    ∧ darkPhaseCount .decagon = 10
    ∧ darkPhaseCount .hendecagon = 11 := by decide

/-! ## Non-intersection: dark walls don't coincide with SM walls -/

/-- The dark walls (5, 6, 7, 10, 11) don't coincide with any SM
boson wall (0, 3, 8). A Bule unit at a dark wall does not satisfy any
SM-boson Skyrms equilibrium, and vice versa. -/
theorem dark_does_not_intersect_sm_bosons (d : DarkSectorParticle) :
    darkPhaseCount d ≠ 0       -- not Higgs (vacuum)
    ∧ darkPhaseCount d ≠ 3     -- not Triton (electroweak)
    ∧ darkPhaseCount d ≠ 8     -- not Octagon (gluons)
    := by
  cases d <;> simp [darkPhaseCount, towerPhaseCount] <;> decide

/-- The dark walls don't coincide with the SM fermion wall (12). -/
theorem dark_does_not_intersect_sm_fermions (d : DarkSectorParticle) :
    darkPhaseCount d ≠ 12 := by
  cases d <;> simp [darkPhaseCount, towerPhaseCount] <;> decide

/-! ## Dark-matter Skyrms equilibrium -/

/-- A Bule unit sits at a dark-sector particle's Skyrms equilibrium
when its score equals the dark wall. -/
def darkSkyrmsEquilibrium (b : BuleyUnit) (d : DarkSectorParticle) : Prop :=
  topologicallySafe b (darkPhaseCount d)

/-- Witness: a score-6 unit at the Hexon wall. -/
theorem hexon_dark_witness (i : Fin 6) :
    darkSkyrmsEquilibrium ⟨2, 2, 2⟩ (.hexon i) := by
  unfold darkSkyrmsEquilibrium topologicallySafe
  show buleyUnitScore (⟨2, 2, 2⟩ : BuleyUnit) = darkPhaseCount (.hexon i)
  simp [darkPhaseCount, towerPhaseCount]
  decide

/-- Witness: a score-10 unit at the Decagon wall (the string-theory
dimension signature, here as a dark candidate). -/
theorem decagon_dark_witness :
    darkSkyrmsEquilibrium ⟨5, 5, 0⟩ .decagon := by
  unfold darkSkyrmsEquilibrium topologicallySafe
  simp [darkPhaseCount, towerPhaseCount]
  decide

/-- Witness: a score-11 unit at the Hendecagon wall (M-theory
dimension signature, here as a dark candidate). -/
theorem hendecagon_dark_witness :
    darkSkyrmsEquilibrium ⟨5, 3, 3⟩ .hendecagon := by
  unfold darkSkyrmsEquilibrium topologicallySafe
  simp [darkPhaseCount, towerPhaseCount]
  decide

/-! ## Dark Energy as Vacuum Reach

Dark energy reads as the *operational presence* of the vacuum
carrier — the structural fact that every Bule unit traces back to the
vacuum via swerve lifts (`vacuum_reaches_any_bule`). The vacuum is
not a dark-sector particle (it's the Higgs). But its pervasive reach
is the dark-energy-like background: a state that "is everywhere"
because every other state is reachable from it. -/

/-- Dark energy as vacuum reach: every Bule unit is reachable from
the vacuum, and the vacuum's score is identically zero. The "energy"
is not a per-state quantity but the *presence* of the unique source
state from which every other state emerges. -/
theorem dark_energy_is_vacuum_reach (b : BuleyUnit) :
    vacuumToBule b = b
    ∧ buleyUnitScore vacuumBuleUnit = 0 :=
  ⟨vacuum_reaches_any_bule b, vacuum_has_zero_score⟩

/-! ## Master theorem: the dark sector catalog -/

/-- The dark sector occupies five distinct phase walls (5, 6, 7, 10,
11), none of which coincide with the SM boson walls (0, 3, 8) or the
SM fermion wall (12). Dark energy is the vacuum's pervasive reach. -/
theorem dark_sector_master :
    -- The Hexon admits a witness
    darkSkyrmsEquilibrium ⟨2, 2, 2⟩ (.hexon 0)
    -- Decagon admits a witness
    ∧ darkSkyrmsEquilibrium ⟨5, 5, 0⟩ .decagon
    -- Hendecagon admits a witness
    ∧ darkSkyrmsEquilibrium ⟨5, 3, 3⟩ .hendecagon
    -- Dark walls don't intersect SM boson walls
    ∧ (∀ d : DarkSectorParticle,
        darkPhaseCount d ≠ 0
        ∧ darkPhaseCount d ≠ 3
        ∧ darkPhaseCount d ≠ 8)
    -- Dark walls don't intersect SM fermion wall
    ∧ (∀ d : DarkSectorParticle, darkPhaseCount d ≠ 12)
    -- Dark energy as vacuum reach
    ∧ vacuumToBule vacuumBuleUnit = vacuumBuleUnit :=
  ⟨hexon_dark_witness 0,
   decagon_dark_witness,
   hendecagon_dark_witness,
   dark_does_not_intersect_sm_bosons,
   dark_does_not_intersect_sm_fermions,
   vacuum_reaches_any_bule vacuumBuleUnit⟩

end DarkSectorEquilibria
end Gnosis
