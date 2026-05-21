import Gnosis.WhyFiveFromGoldenWaveBridge

/-
  WhyFiveRouteOverdetermination.lean
  ==================================

  Burns down the next-exploration target from
  `WhyFiveFromGoldenWaveBridge`: golden, pentagon, and wave routes all
  land on cardinality/order five and the same `TheFive` slots.

  Imports `Gnosis.WhyFiveFromGoldenWaveBridge`. Zero `sorry`, zero new
  `axiom`.
-/

namespace Gnosis
namespace WhyFiveRouteOverdetermination

open WhyFiveFromGoldenDiscriminant
open WhyFiveFromGoldenWaveBridge
open TheFiveIsOne

theorem routes_land_on_five :
    goldenDiscriminant = 5 ∧
    pentagonVertexCount = 5 ∧
    (∀ v : PentagonVertex, rotatePentagonN 5 v = v) ∧
    (∀ m : WhyFiveFromWaves.WaveMode,
      WhyFiveFromWaves.evolve
        (WhyFiveFromWaves.evolve
          (WhyFiveFromWaves.evolve
            (WhyFiveFromWaves.evolve
              (WhyFiveFromWaves.evolve m)))) = m) := by
  exact ⟨goldenDiscriminantIsFive,
    pentagonVertexCount_eq_five,
    rotatePentagon_order_5,
    WhyFiveFromWaves.closesAtFive⟩

theorem route_overdetermination_witness :
    goldenDiscriminant = 5 ∧
    pentagonVertexCount = 5 ∧
    WhyFiveFromWavesBijection.waveModeToFive .OriginalWave =
      pentagonVertexToFive .V0 ∧
    (∀ v : PentagonVertex, fiveToPentagonVertex (pentagonVertexToFive v) = v) ∧
    (∀ m : WhyFiveFromWaves.WaveMode,
      WhyFiveFromWavesBijection.fiveToWaveMode
        (WhyFiveFromWavesBijection.waveModeToFive m) = m) ∧
    (∀ f : TheFive,
      WhyFiveFromWavesBijection.waveModeToFive
        (WhyFiveFromWavesBijection.fiveToWaveMode f) = f) := by
  exact ⟨routes_land_on_five.1,
    routes_land_on_five.2.1,
    wave_and_pentagon_routes_share_thefive_slots.1,
    pentagon_route_uses_same_slots_as_thefive.1,
    WhyFiveFromWavesBijection.wave_mode_thefive_bijection.1,
    WhyFiveFromWavesBijection.wave_mode_thefive_bijection.2⟩

/-! ## Next exploration

The fiveness-route bridge is closed at the discrete constructor level.
The pentagon diagonal/side-ratio geometry is outside this Rustic
module; another Init-only slot theorem would not add information.
-/

end WhyFiveRouteOverdetermination
end Gnosis
