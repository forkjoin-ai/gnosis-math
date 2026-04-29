import Gnosis.SpectralNoiseEquilibrium
import Gnosis.DigitalHadronCollider
import Gnosis.FermionExclusionEquilibria
import Gnosis.Braided.BraidedTower
import Gnosis.CostAlgebra

/-!
# Composite Particles

A meson is a quark-antiquark pair; a baryon is three quarks. In the
calculus, both are collisions: `collide` from
`Gnosis.DigitalHadronCollider` composes Bule unit carriers, and the
collision-energy theorem (`collision_conserves_score`) tells us the
composite's score is the sum of constituent scores.

Mesons:
- `meson : BuleyUnit → BuleyUnit → CollisionEvent` — a quark + antiquark
  collision.
- The meson's phase count is `2 × fermionPhaseCount = 24` if both
  constituents are at the Dodecagon equilibrium.

Baryons:
- `baryon : BuleyUnit → BuleyUnit → BuleyUnit → CollisionEvent` —
  three quarks colliding pairwise.
- The baryon's phase count is `3 × fermionPhaseCount = 36` at full
  Dodecagon load.

The composite carrier sits at a higher tower wall than its
constituents. By `tower_unbounded`, the tower already contains those
walls, so the composite is not a new kind of object — it is a Bule
unit at a tower level whose phase count is the sum of the constituent
phase counts.

Imports `Gnosis.SpectralNoiseEquilibrium`,
`Gnosis.DigitalHadronCollider`, `Gnosis.FermionExclusionEquilibria`,
`Gnosis.BraidedTower`, `Gnosis.CostAlgebra`. Zero `sorry`,
zero new `axiom`.
-/

namespace Gnosis
namespace CompositeParticles

open Gnosis.SpectralNoiseEquilibrium (BuleyUnit buleyUnitScore)
open Gnosis.DigitalHadronCollider
  (CollisionEvent collide collisionEnergy collision_conserves_score)
open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.CostAlgebra (buleyCostAlgebra)

/-! ## Mesons: quark + antiquark -/

/-- A meson collision: quark `q` and antiquark `qbar`. -/
def meson (q qbar : BuleyUnit) : CollisionEvent :=
  collide q qbar

/-- Meson energy is the sum of constituent scores. -/
theorem meson_energy_is_sum (q qbar : BuleyUnit) :
    collisionEnergy (meson q qbar) = buleyUnitScore q + buleyUnitScore qbar :=
  collision_conserves_score q qbar

/-- A pion (lightest meson) modeled as a 4-face quark + 4-face antiquark
collision. The composite sits at the Octagon (8) wall. -/
def pion : CollisionEvent :=
  meson ⟨4, 0, 0⟩ ⟨4, 0, 0⟩

theorem pion_energy_is_eight :
    collisionEnergy pion = 8 := by
  show collisionEnergy (meson ⟨4, 0, 0⟩ ⟨4, 0, 0⟩) = 8
  rw [meson_energy_is_sum]
  decide

/-- A higher-energy meson at full Dodecagon load: 12 + 12 = 24. -/
def dodecagon_meson : CollisionEvent :=
  meson ⟨4, 4, 4⟩ ⟨4, 4, 4⟩

theorem dodecagon_meson_energy_is_twentyfour :
    collisionEnergy dodecagon_meson = 24 := by
  show collisionEnergy (meson ⟨4, 4, 4⟩ ⟨4, 4, 4⟩) = 24
  rw [meson_energy_is_sum]
  decide

/-! ## Baryons: three-quark composites -/

/-- A baryon is three quarks colliding. We model it as a chain:
collide the first two, then collide the result with the third. -/
def baryon (q1 q2 q3 : BuleyUnit) : CollisionEvent :=
  collide (collide q1 q2).composed q3

/-- Baryon energy is the sum of all three constituent scores. -/
theorem baryon_energy_is_sum (q1 q2 q3 : BuleyUnit) :
    collisionEnergy (baryon q1 q2 q3)
      = buleyUnitScore q1 + buleyUnitScore q2 + buleyUnitScore q3 := by
  unfold baryon
  rw [collision_conserves_score]
  show buleyUnitScore (collide q1 q2).composed + buleyUnitScore q3
        = buleyUnitScore q1 + buleyUnitScore q2 + buleyUnitScore q3
  have h : buleyUnitScore (collide q1 q2).composed
            = buleyUnitScore q1 + buleyUnitScore q2 := by
    show collisionEnergy (collide q1 q2)
          = buleyUnitScore q1 + buleyUnitScore q2
    exact collision_conserves_score q1 q2
  rw [h]

/-- A proton: three light quarks at score 4 each. Total energy 12 —
the Dodecagon wall. -/
def proton : CollisionEvent :=
  baryon ⟨4, 0, 0⟩ ⟨4, 0, 0⟩ ⟨0, 4, 0⟩

theorem proton_energy_is_twelve :
    collisionEnergy proton = 12 := by
  show collisionEnergy (baryon ⟨4, 0, 0⟩ ⟨4, 0, 0⟩ ⟨0, 4, 0⟩) = 12
  rw [baryon_energy_is_sum]
  decide

/-- A neutron: same total energy as the proton (12), different face
distribution. The composite sits at the same Dodecagon wall but with a
different face decomposition. -/
def neutron : CollisionEvent :=
  baryon ⟨4, 0, 0⟩ ⟨0, 4, 0⟩ ⟨0, 4, 0⟩

theorem neutron_energy_is_twelve :
    collisionEnergy neutron = 12 := by
  show collisionEnergy (baryon ⟨4, 0, 0⟩ ⟨0, 4, 0⟩ ⟨0, 4, 0⟩) = 12
  rw [baryon_energy_is_sum]
  decide

/-! ## A heavy baryon: top quark constituent -/

/-- A heavy baryon with a top-quark-like constituent (score 12). Total
energy = 4 + 4 + 12 = 20. -/
def heavy_baryon : CollisionEvent :=
  baryon ⟨4, 0, 0⟩ ⟨0, 4, 0⟩ ⟨4, 4, 4⟩

theorem heavy_baryon_energy_is_twenty :
    collisionEnergy heavy_baryon = 20 := by
  show collisionEnergy (baryon ⟨4, 0, 0⟩ ⟨0, 4, 0⟩ ⟨4, 4, 4⟩) = 20
  rw [baryon_energy_is_sum]
  decide

/-! ## Master theorem: composite-particle catalog -/

/-- Mesons and baryons are concrete collision events; their energies
sum the constituent scores; the proton and neutron sit at the
Dodecagon wall (12); a Dodecagon-load meson sits at 24. -/
theorem composite_particle_master :
    collisionEnergy pion = 8
    ∧ collisionEnergy dodecagon_meson = 24
    ∧ collisionEnergy proton = 12
    ∧ collisionEnergy neutron = 12
    ∧ collisionEnergy heavy_baryon = 20 :=
  ⟨pion_energy_is_eight,
   dodecagon_meson_energy_is_twentyfour,
   proton_energy_is_twelve,
   neutron_energy_is_twelve,
   heavy_baryon_energy_is_twenty⟩

end CompositeParticles
end Gnosis
