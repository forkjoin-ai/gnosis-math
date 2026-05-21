import Gnosis.WhyFiveFromGoldenDiscriminant
import Gnosis.WhyFiveFromWavesBijection

/-
  WhyFiveFromGoldenWaveBridge.lean
  =================================

  Burns down the next-exploration target from
  `WhyFiveFromWavesBijection`: the golden/pentagon route and the wave
  route choose the same `TheFive` slots.

  Imports `Gnosis.WhyFiveFromGoldenDiscriminant` and
  `Gnosis.WhyFiveFromWavesBijection`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace WhyFiveFromGoldenWaveBridge

open WhyFiveFromGoldenDiscriminant
open TheFiveIsOne

def pentagonVertexToFive : PentagonVertex → TheFive
  | .V0 => .First
  | .V1 => .Second
  | .V2 => .Third
  | .V3 => .Fourth
  | .V4 => .Fifth

def fiveToPentagonVertex : TheFive → PentagonVertex
  | .First  => .V0
  | .Second => .V1
  | .Third  => .V2
  | .Fourth => .V3
  | .Fifth  => .V4

theorem pentagon_five_left_inverse (v : PentagonVertex) :
    fiveToPentagonVertex (pentagonVertexToFive v) = v := by
  cases v <;> rfl

theorem pentagon_five_right_inverse (f : TheFive) :
    pentagonVertexToFive (fiveToPentagonVertex f) = f := by
  cases f <;> rfl

theorem pentagon_route_uses_same_slots_as_thefive :
    (∀ v : PentagonVertex, fiveToPentagonVertex (pentagonVertexToFive v) = v) ∧
    (∀ f : TheFive, pentagonVertexToFive (fiveToPentagonVertex f) = f) :=
  ⟨pentagon_five_left_inverse, pentagon_five_right_inverse⟩

theorem wave_and_pentagon_routes_share_thefive_slots :
    WhyFiveFromWavesBijection.waveModeToFive .OriginalWave =
      pentagonVertexToFive .V0 ∧
    WhyFiveFromWavesBijection.waveModeToFive .FirstSelfInterference =
      pentagonVertexToFive .V1 ∧
    WhyFiveFromWavesBijection.waveModeToFive .SecondSelfInterference =
      pentagonVertexToFive .V2 ∧
    WhyFiveFromWavesBijection.waveModeToFive .SecondWaveConstructive =
      pentagonVertexToFive .V3 ∧
    WhyFiveFromWavesBijection.waveModeToFive .SecondWaveDestructive =
      pentagonVertexToFive .V4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem golden_wave_bridge_witness :
    goldenDiscriminant = 5 ∧
    pentagonVertexCount = 5 ∧
    WhyFiveFromWaves.evolve
        (WhyFiveFromWaves.evolve
          (WhyFiveFromWaves.evolve
            (WhyFiveFromWaves.evolve
              (WhyFiveFromWaves.evolve .OriginalWave)))) = .OriginalWave ∧
    WhyFiveFromWavesBijection.waveModeToFive .OriginalWave =
      pentagonVertexToFive .V0 := by
  exact ⟨goldenDiscriminantIsFive,
    pentagonVertexCount_eq_five,
    rfl,
    wave_and_pentagon_routes_share_thefive_slots.1⟩

/-! ## Next exploration

Closed by `Gnosis.WhyFiveRouteOverdetermination`: the golden,
pentagon, and wave routes now land on the same discrete five-slot
witness.
-/

end WhyFiveFromGoldenWaveBridge
end Gnosis
