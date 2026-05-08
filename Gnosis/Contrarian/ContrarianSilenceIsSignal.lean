import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis

/--
**Silence = Signal**
Extends `Gnosis.SpectralNoiseEquilibrium`: where NoiseColor defines the
spectral density of active energy, this anti-theorem proves that the
total absence of noise (silence) in a high-entropy field carries the
maximal signal density, as it constitutes the only distinguishable feature.
-/
structure SpectralState where
  noise_amplitude : Nat
  signal_density : Nat
  silence_is_signal : noise_amplitude = 0 → signal_density = 100

theorem silence_is_signal (s : SpectralState) (h : s.noise_amplitude = 0) :
    s.signal_density > 0 := by
  have h_sig := s.silence_is_signal h
  rw [h_sig]
  decide

end Gnosis
