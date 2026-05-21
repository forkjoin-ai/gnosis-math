import Gnosis.WhyFiveFromWaves
import Gnosis.TheFiveIsOne

/-
  WhyFiveFromWavesBijection.lean
  ==============================

  Burns down the future-bijection note from `WhyFiveFromWaves` by
  wiring each `WaveMode` constructor to the corresponding `TheFive`
  slot and proving both round trips.

  Zero `sorry`, zero new `axiom`.
-/

namespace WhyFiveFromWavesBijection

open WhyFiveFromWaves
open TheFiveIsOne

def waveModeToFive : WaveMode → TheFive
  | .OriginalWave           => .First
  | .FirstSelfInterference  => .Second
  | .SecondSelfInterference => .Third
  | .SecondWaveConstructive => .Fourth
  | .SecondWaveDestructive  => .Fifth

def fiveToWaveMode : TheFive → WaveMode
  | .First  => .OriginalWave
  | .Second => .FirstSelfInterference
  | .Third  => .SecondSelfInterference
  | .Fourth => .SecondWaveConstructive
  | .Fifth  => .SecondWaveDestructive

theorem fiveToWaveMode_left_inverse (m : WaveMode) :
    fiveToWaveMode (waveModeToFive m) = m := by
  cases m <;> rfl

theorem waveModeToFive_left_inverse (f : TheFive) :
    waveModeToFive (fiveToWaveMode f) = f := by
  cases f <;> rfl

theorem wave_mode_thefive_bijection :
    (∀ m : WaveMode, fiveToWaveMode (waveModeToFive m) = m) ∧
    (∀ f : TheFive, waveModeToFive (fiveToWaveMode f) = f) :=
  ⟨fiveToWaveMode_left_inverse, waveModeToFive_left_inverse⟩

theorem wave_evolve_matches_thefive_order :
    waveModeToFive (evolve .OriginalWave) = .Second ∧
    waveModeToFive (evolve .FirstSelfInterference) = .Third ∧
    waveModeToFive (evolve .SecondSelfInterference) = .Fourth ∧
    waveModeToFive (evolve .SecondWaveConstructive) = .Fifth ∧
    waveModeToFive (evolve .SecondWaveDestructive) = .First := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Next exploration

Closed by `Gnosis.WhyFiveFromGoldenWaveBridge`: the constructor
bijection now agrees with the golden-route `TheFive` slots.
-/

end WhyFiveFromWavesBijection
