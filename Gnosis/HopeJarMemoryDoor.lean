/-
  HopeJarMemoryDoor
  =================

  The certified memory-mapping transition for the hybrid Hope Jar.

  The benchmark surfaced a real problem: an E_8 jar slot is 96768 keys
  (≈774 KB). Memoizing every touched slot blows resident memory past the
  Monster jar's whole footprint after ~2 slots. The fix is not to cache
  every slot — it is to cache a slot only when caching PAYS, and only
  within a memory budget. That "pays" decision is exactly the value-door
  crossover (`ValueDoorStoplight`), and the crossover IS the transition.

  The transition (cache ⇄ regenerate)
  -----------------------------------
  For a slot accessed `n` times:
    * regenerate (latent, no RAM): cost  n · regenPerAccess
    * materialize (cache, pay RAM): cost  memPrice + n · readPerAccess
  With readPerAccess < regenPerAccess the cache cost grows slower, so above
  a crossover access count the door flips RED→GREEN: below it, regenerate
  (laminar / latent); above it, materialize (turbulent / cached). This is
  the Reynolds-style transition the hybrid was missing.

  The fix (bounded resident memory)
  ---------------------------------
  Admit a slot to the resident cache only when it is GREEN and it still
  fits the budget. `resident_bounded` proves the resident key count never
  exceeds the budget — for ANY access pattern, ANY number of green slots.
  With the Monster jar's footprint as the budget, the hybrid provably never
  exceeds Monster's RAM (`hybrid_never_exceeds_monster`), the 50 MB blow-up
  fixed by construction.

  Reuses `ValueDoorStoplight.light` / `certified_never_yellow`. No sorry,
  no new axioms.
-/

import Gnosis.ValueDoorStoplight

namespace HopeJarMemoryDoor

open ValueDoorStoplight

/-- An E_8 jar slot is 96768 keys — the ≈774 KB unit the benchmark flagged. -/
def e8SlotKeys : Nat := 96768

-- ══════════════════════════════════════════════════════════
-- THE TWO STRATEGY COSTS  (abstract Nat units: ns, cycles, …)
-- ══════════════════════════════════════════════════════════

/-- Cost of REGENERATING the slot on every one of `n` accesses (latent,
    zero resident memory). -/
def recomputeCost (regenPerAccess n : Nat) : Nat := n * regenPerAccess

/-- Cost of MATERIALIZING the slot once and reading it: a one-time memory
    price plus a cheap read per access. -/
def gateCost (memPrice readPerAccess n : Nat) : Nat := memPrice + n * readPerAccess

-- ══════════════════════════════════════════════════════════
-- THE MEMORY-MAPPING VALUE-DOOR
-- ══════════════════════════════════════════════════════════

/-- The memory door: colour the cache-vs-regenerate decision by the
    value-door crossover. GREEN = caching pays (materialize); RED = regenerate. -/
def memoryDoor (memPrice readPerAccess regenPerAccess n : Nat) : Light :=
  light (some (recomputeCost regenPerAccess n)) (gateCost memPrice readPerAccess n)

/-- The decision is always definite — never YELLOW. The cost is read from
    the slot's size + access count (a cert), so there is no probe state. -/
theorem memory_door_never_yellow (mp rd rg n : Nat) :
    memoryDoor mp rd rg n ≠ Light.yellow :=
  certified_never_yellow _ _

/-- GREEN exactly when caching is cheaper than regenerating. -/
theorem cache_green_iff (mp rd rg n : Nat) :
    memoryDoor mp rd rg n = Light.green ↔ gateCost mp rd n < recomputeCost rg n := by
  unfold memoryDoor; simp only [light]
  by_cases h : gateCost mp rd n < recomputeCost rg n
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh h⟩

-- ══════════════════════════════════════════════════════════
-- THE TRANSITION  (RED below the crossover, GREEN above)
-- ══════════════════════════════════════════════════════════

/-- Below the crossover — regenerate cost not yet beaten — the door is RED:
    keep the slot latent, spend no resident memory. -/
theorem transition_red_below (mp rd rg n : Nat)
    (h : n * rg ≤ mp + n * rd) :
    memoryDoor mp rd rg n = Light.red := by
  unfold memoryDoor recomputeCost gateCost; simp only [light]
  rw [if_neg (Nat.not_lt.mpr h)]

/-- Above the crossover — enough accesses that the one-time memory price is
    amortized away — the door is GREEN: materialize the slot. -/
theorem transition_green_above (mp rd rg n : Nat)
    (h : mp + n * rd < n * rg) :
    memoryDoor mp rd rg n = Light.green := by
  unfold memoryDoor recomputeCost gateCost; simp only [light]
  rw [if_pos h]

/-- The transition is monotone in accesses: once the door is GREEN at `n`
    accesses it stays GREEN at `n+1` (more hits only help the cache), given
    reads are cheaper than regenerates. So there is a single crossover, not
    an oscillation. -/
theorem transition_monotone (mp rd rg n : Nat) (hrr : rd < rg)
    (hg : memoryDoor mp rd rg n = Light.green) :
    memoryDoor mp rd rg (n + 1) = Light.green := by
  rw [cache_green_iff] at hg ⊢
  unfold gateCost recomputeCost at hg ⊢
  -- hg : mp + n*rd < n*rg ;  goal : mp + (n+1)*rd < (n+1)*rg
  have e1 : (n + 1) * rd = n * rd + rd := Nat.succ_mul n rd
  have e2 : (n + 1) * rg = n * rg + rg := Nat.succ_mul n rg
  rw [e1, e2]; omega

-- ══════════════════════════════════════════════════════════
-- THE FIX:  RESIDENT MEMORY IS BOUNDED BY THE BUDGET
-- ══════════════════════════════════════════════════════════

/-- Admit one slot's keys to the resident cache iff it is GREEN and still
    fits the budget. -/
def residentStep (budget resident : Nat) (green : Bool) : Nat :=
  if green = true ∧ resident + e8SlotKeys ≤ budget then resident + e8SlotKeys else resident

/-- Resident key count after greedily admitting a stream of slots (each
    flagged GREEN or not) under a fixed key budget. -/
def residentKeys (budget : Nat) (greens : List Bool) : Nat :=
  greens.foldl (residentStep budget) 0

/-- One admission preserves the budget invariant. -/
theorem residentStep_le (budget resident : Nat) (g : Bool) (h : resident ≤ budget) :
    residentStep budget resident g ≤ budget := by
  unfold residentStep
  by_cases hc : g = true ∧ resident + e8SlotKeys ≤ budget
  · rw [if_pos hc]; exact hc.2
  · rw [if_neg hc]; exact h

theorem residentKeys_foldl_le (budget : Nat) (greens : List Bool) :
    ∀ acc, acc ≤ budget → greens.foldl (residentStep budget) acc ≤ budget := by
  induction greens with
  | nil => intro acc h; exact h
  | cons g rest ih =>
    intro acc h
    exact ih _ (residentStep_le budget acc g h)

/-- **The fix.** No matter the access pattern, no matter how many slots go
    GREEN, the resident cache never exceeds the budget. The 50 MB blow-up
    cannot happen under the door + budget. -/
theorem resident_bounded (budget : Nat) (greens : List Bool) :
    residentKeys budget greens ≤ budget :=
  residentKeys_foldl_le budget greens 0 (Nat.zero_le budget)

-- ══════════════════════════════════════════════════════════
-- TIE TO THE BENCHMARK NUMBERS
-- ══════════════════════════════════════════════════════════

/-- The Monster jar's 196884-key footprint, used as the hybrid's budget. -/
def monsterBudgetKeys : Nat := 196884

/-- At most 2 whole E_8 slots fit Monster's footprint — exactly the "~2.0"
    the benchmark measured (`196884 / 96768 = 2`). -/
theorem e8_slots_in_monster_budget : monsterBudgetKeys / e8SlotKeys = 2 := by
  native_decide

/-- With Monster's footprint as the budget, the hybrid provably never exceeds
    Monster's RAM — the memory-mapping issue fixed by construction. -/
theorem hybrid_never_exceeds_monster (greens : List Bool) :
    residentKeys monsterBudgetKeys greens ≤ monsterBudgetKeys :=
  resident_bounded _ _

/-- **Master.** The certified memory door: a never-yellow cache/regenerate
    decision, a monotone single transition, and a hard resident-memory bound
    under any access pattern. -/
theorem memory_door_master (mp rd rg n : Nat) (greens : List Bool) :
    memoryDoor mp rd rg n ≠ Light.yellow
    ∧ residentKeys monsterBudgetKeys greens ≤ monsterBudgetKeys :=
  ⟨memory_door_never_yellow mp rd rg n, hybrid_never_exceeds_monster greens⟩

end HopeJarMemoryDoor
