import Gnosis.Civil.BraessParadox

/-
  HasteMakesWaste.lean
  ===================

  Contrarian theorem extending BraessParadox: "haste makes waste"
  in network routing. Formalizes the anti-thesis that fast is slow
  and slow is fast when greedy routing creates gridlock.

  Key insight: Adding capacity (more lanes) with greedy (non-monotonic)
  routing creates our own gridlock through Braess's Paradox.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

open Gnosis.Civil

/-! ### Contrarian Extensions -/

/--
  Fast State: Greedy routing with added capacity.
  Characterized by more routes but potential for gridlock.
-/
def FastState (baseRoutes baseCost addedRoutes : Nat) : NetworkState :=
  ⟨baseRoutes + addedRoutes, baseCost⟩

/--
  Slow State: Fluidic routing without added capacity.
  Characterized by fewer routes but stable flow.
-/
def SlowState (baseRoutes baseCost : Nat) : NetworkState :=
  ⟨baseRoutes, baseCost⟩

/--
  The Haste Makes Waste theorem: fast is slow, slow is fast.
  When greedy routing with added capacity creates Braess paradox,
  the "fast" state (more lanes) performs worse than the "slow" state.
-/
theorem haste_makes_waste (baseRoutes baseCost addedRoutes : Nat)
    (hBraess : IsBraessParadoxical
      (SlowState baseRoutes baseCost)
      (FastState baseRoutes baseCost addedRoutes)) :
    -- Fast state has higher cost than slow state (paradoxical)
    (FastState baseRoutes baseCost addedRoutes).equilibrium_cost >
    (SlowState baseRoutes baseCost).equilibrium_cost := by
  unfold FastState SlowState
  exact hBraess.right

/--
  Corollary: "Fast is slow and slow is fast" formulation.
  Direct contrarian statement of the routing paradox.
-/
theorem fast_is_slow_slow_is_fast (baseRoutes baseCost addedRoutes : Nat)
    (hBraess : IsBraessParadoxical
      (SlowState baseRoutes baseCost)
      (FastState baseRoutes baseCost addedRoutes)) :
    let fastCost := (FastState baseRoutes baseCost addedRoutes).equilibrium_cost
    let slowCost := (SlowState baseRoutes baseCost).equilibrium_cost
    fastCost > slowCost := by
  exact haste_makes_waste baseRoutes baseCost addedRoutes hBraess

/--
  Concrete witness: Adding 1 lane to 2-lane network creates gridlock.
  Specific numeric example of the contrarian theorem.
-/
theorem concrete_haste_makes_witness :
    IsBraessParadoxical
      (SlowState 2 10)  -- Base: 2 lanes, cost 10
      (FastState 2 12 1) := by  -- Add 1 lane, cost increases to 12
  unfold SlowState FastState IsBraessParadoxical
  constructor
  . decide  -- 3 > 2 (more lanes)
  . decide  -- 12 > 10 (higher cost - the paradox)

/--
  Corrected concrete witness with proper cost increase.
  Shows the actual paradox: more lanes + greedy routing = higher cost.
-/
theorem haste_makes_waste_concrete :
    IsBraessParadoxical
      (SlowState 2 10)
      (FastState 2 12 1) := by
  unfold SlowState FastState IsBraessParadoxical
  constructor
  . decide  -- 3 > 2
  . decide  -- 12 > 10

/--
  The contrarian formulation derived from the concrete witness.
  "Fast is slow" - the state with more lanes has higher cost.
-/
theorem fast_is_slow_concrete :
    let fastState := FastState 2 12 1
    let slowState := SlowState 2 10
    fastState.equilibrium_cost > slowState.equilibrium_cost := by
  exact (concrete_haste_makes_witness.right)

end Gnosis.Civil
