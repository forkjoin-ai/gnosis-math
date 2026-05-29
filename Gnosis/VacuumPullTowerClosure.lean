import Gnosis.SpectralNoiseEquilibrium

/-! # Vacuum Pull Tower Closure

Finite compatibility surface for `VacuumPullTowerClosureMechanism`.
The witness is concrete: the exported vacuum carrier is exactly the
`vacuumBuleUnit` supplied by `SpectralNoiseEquilibrium`.
-/

namespace Gnosis
namespace VacuumPullTowerClosure

open SpectralNoiseEquilibrium

theorem vacuum_exists : ∃ b : BuleyUnit, b = vacuumBuleUnit :=
  ⟨vacuumBuleUnit, rfl⟩

end VacuumPullTowerClosure
end Gnosis
