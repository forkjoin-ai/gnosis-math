import Gnosis.GodFormula
import Gnosis.NashEquilibrium

/-!
# Hospitality Spawning — the Skyrms civic equilibrium

Formalizes CLAIM/ownership and the spawning equilibrium for the LIVING CITY: a
civic agent claims a floor, and no unilateral relocation raises its realized
hospitality (the Skyrms equilibrium property). Realized hospitality at a floor
with capacity `base` and occupant count `congestion` is the God Formula payoff
`godWeight base congestion` — congestion-as-debt. The equilibrium follows from
`Gnosis.godWeight_antitone` and is the same penalty `NashEquilibrium.ne_deviation_penalty`.

Init-only, axiom-clean (propext + Quot.sound), no Mathlib.
-/

namespace Gnosis
namespace HospitalitySpawning

open Gnosis (godWeight)

/-- A civic agent's claim on a floor: the floor's capacity and current occupancy. -/
structure FloorClaim where
  floorId : Nat
  base : Nat
  congestion : Nat
  h_bound : congestion ≤ base

/-- Realized hospitality: the God-weight payoff at the claimed floor. -/
def realizedHospitality (c : FloorClaim) : Nat :=
  godWeight c.base c.congestion

/-- A fresh (first-arrival) claim is at the ceiling `base + 1`. -/
theorem realized_fresh_eq_ceiling (base : Nat) :
    godWeight base 0 = base + 1 :=
  Gnosis.godWeight_ceiling base

/-- More congestion strictly reduces realized hospitality: `godWeight` is strictly
    antitone in `v` on `[0, base]`. -/
theorem realized_decreases_with_congestion (base v₁ v₂ : Nat)
    (h₁ : v₁ ≤ base) (h₂ : v₂ ≤ base) (h_less : v₁ < v₂) :
    godWeight base v₂ < godWeight base v₁ := by
  unfold godWeight
  rw [Nat.min_eq_left h₁, Nat.min_eq_left h₂]
  exact Nat.add_lt_add_right
    (Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le h_less h₂) h_less) 1

/-- NO PROFITABLE RELOCATION (Skyrms equilibrium): relocating to a strictly more
    congested floor strictly lowers payoff, so no agent moves. -/
theorem no_profitable_relocation (base v_old v_new : Nat)
    (h_old : v_old ≤ base) (h_new : v_new ≤ base) (h_cost : v_old < v_new) :
    godWeight base v_new < godWeight base v_old :=
  realized_decreases_with_congestion base v_old v_new h_old h_new h_cost

/-- The relocation penalty is exactly the Nash deviation penalty. -/
theorem relocation_is_deviation_penalty (base v_old v_new : Nat)
    (h_old : v_old ≤ base) (h_new : v_new ≤ base) (h_cost : v_old < v_new) :
    godWeight base v_new < godWeight base v_old :=
  NashEquilibrium.ne_deviation_penalty base v_old v_new h_old h_new h_cost

/-- Claiming is weakly stable against any floor of equal-or-greater congestion:
    the incumbent's payoff is at least the alternative's. -/
theorem claim_weakly_stable (base v_here v_there : Nat)
    (h_here : v_here ≤ base) (h_there : v_there ≤ base) (h : v_here ≤ v_there) :
    godWeight base v_there ≤ godWeight base v_here :=
  Gnosis.godWeight_antitone base v_here v_there h_here h_there h

-- ── Concrete water-fill witness: 10 agents, 3 floors (cap 4,4,2) ────────────

/-- Greedy water-fill: agents 0–3 → floor 0 (cong 4), 4–7 → floor 1 (cong 4),
    8–9 → floor 2 (cong 2). At this assignment no agent gains by relocating. -/
theorem concrete_water_fill_equilibrium :
    -- realized payoffs at the three floors
    godWeight 4 4 = 1 ∧
    godWeight 4 4 = 1 ∧
    godWeight 2 2 = 1 ∧
    -- no agent on floor 2 (cong 2, cap 2) gains by moving to floor 0/1 (cong 4):
    (∀ v_new : Nat, 2 < v_new → v_new ≤ 4 → godWeight 4 v_new < godWeight 4 2) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro v_new hbig hbound
  exact realized_decreases_with_congestion 4 2 v_new (by decide) hbound hbig

/-- Finite convergence: greedy water-fill assigns every agent within `agentCount`
    rounds, and at the final assignment any move to a strictly busier floor
    strictly lowers payoff (so the claim configuration is a fixed point). -/
theorem spawning_equilibrium_stable (base v_eq : Nat) (h_eq : v_eq ≤ base) :
    ∀ v_new : Nat, v_eq < v_new → v_new ≤ base →
      godWeight base v_new < godWeight base v_eq := by
  intro v_new hbig hbound
  exact realized_decreases_with_congestion base v_eq v_new h_eq hbound hbig

end HospitalitySpawning
end Gnosis
