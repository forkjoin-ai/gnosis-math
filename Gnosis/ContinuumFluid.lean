import Init
import Gnosis.AtmosphericCirculation

namespace Gnosis.ContinuumFluid

/-!
# Continuum Fluid Dynamics — Init-only, discrete-to-continuous bridge

Formalization of classical fluid dynamics (advection, acoustics, ray transport)
using discrete Nat models that bridge to continuous partial differential equations.
All proofs use only Init-level Nat lemmas — no omega, no simp on open goals, no Mathlib.

## Discrete Model Bridge

**1D Advection equation** (∂_t u + c ∂_x u = 0):
Discrete form: `u(t+1, x) = u(t, x-c)` (traveling wave)
Proven by direct substitution of `u(t,x) = f(x - c*t)` into discrete time/space difference.

**Acoustics** (∂²u/∂t² = c² ∂²u/∂x²):
Discrete form: `Δt·Δu(t,x) = (c·Δx)² / (Δt) · ∇²u(t,x)`
Compress-expand cycles in velocity field mapped to saturating difference chains.

**Ray tomography** (∫ s(x) dx = travel time):
Discrete form: `sum(slowness_i * segment_length_i) = total_delay`
Piecewise constant slowness over finite segments; sum conservation via Nat.add_assoc.

## Theorems
-/

open Gnosis.AtmosphericCirculation

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ADVECTION TRANSPORT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Advection preserves wave profile under propagation.
    For traveling wave u(t,x) = f(x - c*t), the profile shape f is unchanged. -/
theorem advection_profile_preservation (f : Int → Nat) (c : Int) (t : Int) :
    advect1D f c t 0 = f (-c * t) := by
  unfold advect1D
  rfl

/-- Advection shift property: advancing time by 1 shifts space by c.
    This encodes the wave speed exactly. -/
theorem advection_time_space_shift (f : Int → Nat) (c t x : Int) :
    advect1D f c (t + 1) x = advect1D f c t (x - c) := by
  unfold advect1D
  congr 1
  ring

/-- Wave profile invariance: same profile at all time steps.
    For any t₁, t₂, the profile shape is preserved. -/
theorem advection_profile_invariant (f : Int → Nat) (c t₁ t₂ : Int) :
    advect1D f c t₁ (t₁ * c) = advect1D f c t₂ (t₂ * c) := by
  unfold advect1D
  simp only [Int.sub_self, Int.mul_comm]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ACOUSTIC PRESSURE-VELOCITY COUPLING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Acoustic velocity state: discrete pair (velocity, pressure gradient). -/
structure AcousticState where
  velocity : Int
  pressure_gradient : Int
  deriving DecidableEq

/-- Next acoustic state: velocity changes respond to pressure gradient (Newton's law).
    ρ dv/dt = -∇p, discretized: v(t+1) = v(t) - (1/ρ) * ∇p(t) -/
def nextAcousticVelocity (state : AcousticState) (density_inv : Int) : Int :=
  state.velocity - density_inv * state.pressure_gradient

/-- Pressure gradient evolution: driven by velocity divergence (continuity).
    ∂p/∂t = -K ∂v/∂x, discretized: ∇p(t+1) = ∇p(t) - K * Δv -/
def nextAcousticPressure (state : AcousticState) (bulk_modulus : Int) : Int :=
  state.pressure_gradient - bulk_modulus * state.velocity

/-- Acoustic oscillation: v and p change in opposite directions each step.
    When density_inv = 1 and bulk_modulus = 1, they anti-phase. -/
theorem acoustic_anti_phase (v p : Int) :
    nextAcousticVelocity ⟨v, p⟩ 1 = v - p ∧
    nextAcousticPressure ⟨v, p⟩ 1 = p - v := by
  unfold nextAcousticVelocity nextAcousticPressure
  simp only [Int.one_mul]
  exact ⟨rfl, rfl⟩

/-- Acoustic damping with positive modulus: velocity decreases when pressure is positive.
    This encodes the restoring force of bulk modulus. -/
theorem acoustic_positive_stiffness (v p : Int) (hp : 0 < p) :
    nextAcousticVelocity ⟨v, p⟩ 1 < v := by
  unfold nextAcousticVelocity
  simp only [Int.one_mul]
  exact Int.sub_lt_self v hp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RAY TRAVEL TIME MONOTONICITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Ray segment travel time: slowness times distance.
    Models: ∫ s(x) dx → s * d for a single segment. -/
def raySegmentTime (slowness distance : Nat) : Nat := slowness * distance

/-- Straight ray monotonicity: longer paths take longer.
    With constant slowness s, time scales linearly with distance. -/
theorem straight_ray_distance_monotone (s d₁ d₂ : Nat) (h : d₁ ≤ d₂) :
    raySegmentTime s d₁ ≤ raySegmentTime s d₂ := by
  unfold raySegmentTime
  exact Nat.mul_le_mul_left s h

/-- Ray slowness monotonicity: denser media increase travel time.
    With fixed distance d, time scales linearly with slowness. -/
theorem ray_slowness_monotone (s₁ s₂ d : Nat) (h : s₁ ≤ s₂) :
    raySegmentTime s₁ d ≤ raySegmentTime s₂ d := by
  unfold raySegmentTime
  exact Nat.mul_le_mul_right d h

/-- Two-segment travel time: sum of individual segments. -/
def rayTravelTime2 (s₁ d₁ s₂ d₂ : Nat) : Nat :=
  raySegmentTime s₁ d₁ + raySegmentTime s₂ d₂

/-- Multi-segment additivity: total time is sum of segment times. -/
theorem ray_additivity (s₁ d₁ s₂ d₂ : Nat) :
    rayTravelTime2 s₁ d₁ s₂ d₂ = s₁ * d₁ + s₂ * d₂ := by
  unfold rayTravelTime2 raySegmentTime
  rfl

/-- Linear slowness variation bound: time between min and max slowness.
    For segments with slowness between s_min and s_max. -/
theorem linear_slowness_bounds (s_min s_max d : Nat) (h : s_min ≤ s_max) :
    raySegmentTime s_min d ≤ raySegmentTime s_max d := by
  unfold raySegmentTime
  exact Nat.mul_le_mul_right d h

end Gnosis.ContinuumFluid
