namespace CrossDomainOceanographyMusicBridge

structure OceanographyMusicAdapter where
  tidal_resonance : Nat
  harmonic_frequency : Nat
  wave_amplitude : Nat
  h_wave : wave_amplitude = tidal_resonance + harmonic_frequency * tidal_resonance

theorem wave_amplitude_bound (adapter : OceanographyMusicAdapter) :
  adapter.wave_amplitude ≥ adapter.tidal_resonance := by
  rw [adapter.h_wave]
  exact Nat.le_add_right adapter.tidal_resonance (adapter.harmonic_frequency * adapter.tidal_resonance)

end CrossDomainOceanographyMusicBridge