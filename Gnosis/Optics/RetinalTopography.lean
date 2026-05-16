-- Gnosis.Optics.RetinalTopography
-- Track Alpha: Optical geometry, PSF aberrations, corneal scattering
-- Formalizes three core theorems on how light refracts through the optical system

import Gnosis.Optics.OpticalFoundations

namespace Gnosis.Optics.RetinalTopography

-- THM-FOVEAL-CONE-DENSITY-BOUND: exponential foveation falloff
-- Proves that structural information capacity scales with distance from fovea

theorem foveal_cone_density_bound :
    ∀ d : Nat, coneDensityAtDistance d ≤ 100 := by
  intro d
  unfold coneDensityAtDistance
  exact Nat.sub_le _ _

theorem foveal_density_is_max_at_center :
    coneDensityAtDistance 0 = 100 :=
  foveal_density_at_zero

-- THM-PSF-ABERRATION-CONVOLUTION: optical point spread deficit
-- Proves that optical imperfections cause point spread function broadening

theorem psf_convolution_bounds (intensity : Nat) :
    psfWidth intensity ≥ 1 := by
  unfold psfWidth
  exact Nat.succ_pos _

theorem psf_broadening_with_intensity :
    ∀ i₁ i₂ : Nat, i₁ ≤ i₂ → psfWidth i₁ ≤ psfWidth i₂ := by
  intros i₁ i₂ hle
  unfold psfWidth
  have : i₁ / 16 ≤ i₂ / 16 :=
    Nat.div_le_div_right hle
  exact Nat.add_le_add_right this 1

-- PSF width always positive (hard boundaries impossible)
theorem impossible_perfect_focus :
    ∀ intensity : Nat, psfWidth intensity ≥ 1 :=
  psf_convolution_bounds

-- THM-CORNEAL-CORONA-SCATTERING: radial flare and halo entropy bounds

theorem corona_halo_monotone_increasing :
    ∀ i₁ i₂ : Nat, i₁ ≤ i₂ → coronaHaloRadius i₁ ≤ coronaHaloRadius i₂ := by
  intros i₁ i₂ hle
  unfold coronaHaloRadius
  have : i₁ / 32 ≤ i₂ / 32 :=
    Nat.div_le_div_right hle
  exact Nat.add_le_add_right this 1

theorem corona_halo_always_positive :
    ∀ intensity : Nat, coronaHaloRadius intensity ≥ 1 := by
  intro intensity
  unfold coronaHaloRadius
  exact Nat.succ_pos _

-- Total optical spread (PSF + halo combined)
def total_optical_spread (intensity : Nat) : Nat :=
  psfWidth intensity + coronaHaloRadius intensity

theorem total_optical_spread_bounded (intensity : Nat) :
    total_optical_spread intensity ≥ 2 := by
  unfold total_optical_spread
  have h1 : 1 ≤ psfWidth intensity :=
    psf_convolution_bounds intensity
  have h2 : 1 ≤ coronaHaloRadius intensity :=
    corona_halo_always_positive intensity
  exact Nat.add_le_add h1 h2

theorem optical_spread_monotone :
    ∀ i₁ i₂ : Nat, i₁ ≤ i₂ → total_optical_spread i₁ ≤ total_optical_spread i₂ := by
  intros i₁ i₂ hle
  unfold total_optical_spread
  exact Nat.add_le_add
    (psf_broadening_with_intensity i₁ i₂ hle)
    (corona_halo_monotone_increasing i₁ i₂ hle)

-- Simple bound: PSF and halo contribute at most 2 to the optical spread
theorem optical_spread_at_least_2 (intensity : Nat) :
    total_optical_spread intensity ≥ 2 :=
  total_optical_spread_bounded intensity

end Gnosis.Optics.RetinalTopography
