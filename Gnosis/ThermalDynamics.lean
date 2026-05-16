import Init
import Gnosis.AtmosphericCirculation

namespace Gnosis.ThermalDynamics

/-!
# Thermal Dynamics: SST, Diffusion, and Shear Barriers

Formalization of ocean thermal processes using discrete meteorological
variables mapped to Nat via saturating arithmetic. Three core theorems
establish monotonicity relationships between buoyancy flux, heat diffusion,
and wind shear.

All proofs use only Init-level Nat lemmas — no omega, no simp on open
goals, no Mathlib axioms.
-/

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CORE DEFINITIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Sea surface temperature (SST) buoyancy flux: difference drives convection.
    Warmer SST minus the minimum of cool SST and warm SST yields the gradient
    that drives vertical motion. -/
def buoyancy_flux (sst_warm sst_cool : Nat) : Nat :=
  sst_warm - min sst_cool sst_warm

/-- Heat diffusion monotonicity: warmer source yields stronger diffusion.
    Heat flows from hot to cold; the gradient magnitude equals the hot
    temperature minus the minimum of both temperatures. -/
def heat_diffuse (t_hot t_cold : Nat) : Nat :=
  t_hot - min t_cold t_hot

/-- Heat transport through layer with shear barrier.
    Shear wind suppresses thermal transport by blocking convection.
    Net transport is SST minus the minimum of shear and SST. -/
def heat_transport (sst shear : Nat) : Nat :=
  sst - min shear sst

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- THEOREM 1: SST Buoyancy Monotonicity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- SST buoyancy flux monotonicity: larger warm-cool gradient yields
    larger buoyancy flux. When sst_warm₁ ≤ sst_warm₂, the flux increases
    monotonically. -/
theorem sst_buoyancy_monotone (sst_cool sst_warm₁ sst_warm₂ : Nat)
    (h : sst_warm₁ ≤ sst_warm₂) :
    buoyancy_flux sst_warm₁ sst_cool ≤ buoyancy_flux sst_warm₂ sst_cool := by
  unfold buoyancy_flux
  by_cases h_cool : sst_cool ≤ sst_warm₁
  · by_cases h_cool2 : sst_cool ≤ sst_warm₂
    · rw [Nat.min_eq_left h_cool, Nat.min_eq_left h_cool2]
      exact Nat.sub_le_sub_right h sst_cool
    · exact (h_cool2 (Nat.le_trans h_cool h)).elim
  · by_cases h_cool2 : sst_cool ≤ sst_warm₂
    · rw [Nat.min_eq_right (Nat.le_of_not_le h_cool), Nat.min_eq_left h_cool2]
      simp only [Nat.sub_self]
      exact Nat.zero_le _
    · rw [Nat.min_eq_right (Nat.le_of_not_le h_cool), Nat.min_eq_right (Nat.le_of_not_le h_cool2)]
      simp only [Nat.sub_self]
      exact Nat.le_refl _

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- THEOREM 2: Heat Diffusion Morphism
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Heat diffusion and buoyancy flux share the same arithmetic form:
    both map two temperatures to their difference via Nat.sub and Nat.min.
    When the domains are aligned, the functions are equivalent. -/
theorem heat_diffusion_morphism (t_hot t_cold : Nat) :
    heat_diffuse t_hot t_cold = buoyancy_flux t_hot t_cold := by
  unfold heat_diffuse buoyancy_flux
  rfl

/-- Direct consequence: diffusion equals buoyancy when flux domains align. -/
theorem diffusion_buoyancy_equivalence (t : Nat) (t₀ : Nat) :
    heat_diffuse t t₀ = t - min t₀ t := by
  unfold heat_diffuse
  rfl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- THEOREM 3: Wind Shear Suppression
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- High shear suppresses heat transport: increasing shear reduces the net
    transport through the layer. When shear₁ ≤ shear₂, the heat transport
    from shear₂ is less than from shear₁. -/
theorem wind_barrier_suppression (sst shear₁ shear₂ : Nat)
    (h : shear₁ ≤ shear₂) :
    heat_transport sst shear₂ ≤ heat_transport sst shear₁ := by
  unfold heat_transport
  by_cases h1 : shear₁ ≤ sst
  · by_cases h2 : shear₂ ≤ sst
    · rw [Nat.min_eq_left h2, Nat.min_eq_left h1]
      exact Nat.sub_le_sub_left h sst
    · rw [Nat.min_eq_right (Nat.le_of_not_le h2), Nat.min_eq_left h1]
      simp only [Nat.sub_self]
      exact Nat.zero_le _
  · by_cases h2 : shear₂ ≤ sst
    · have : shear₁ ≤ sst := Nat.le_trans h h2
      exact (h1 this).elim
    · rw [Nat.min_eq_right (Nat.le_of_not_le h2), Nat.min_eq_right (Nat.le_of_not_le h1)]
      simp only [Nat.sub_self]
      exact Nat.le_refl _

end Gnosis.ThermalDynamics
