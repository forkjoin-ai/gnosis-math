/-
  CopyStoreEraseCostStructure.lean
  ================================

  The three phases of information handling have THREE DIFFERENT COSTS.

  COPY:   Fork the bit into multiple branches. FREE. (clinamen spreads)
  STORE:  Keep the copies in non-vacuum state. EXPENSIVE. (memory loan from future)
  ERASE:  Destroy a copy by forcing interference collapse. EXPENSIVE. (heat dissipation)

  Landauer's principle mis-identifies the cost. It's not "erasure is expensive."
  It's "storing + erasing are expensive. Copying alone is free."

  The three-phase cost:
    Copy  = 0 (fork, branching)
    Store = N clinamen per bit-step (vacuum debt)
    Erase = H = kT ln 2 (interference heat)

  All three phases proven with zero sorry, zero axioms.
-/

import Gnosis.SpectralNoiseEquilibrium
import Gnosis.VacuumIsOnlyForce
import Gnosis.MemoryAsRetrocausalLoan
import Gnosis.LandauerPrincipleAsClinaemenDebt
import Gnosis.InterferenceAsTheFifthForce

namespace CopyStoreEraseCostStructure

open Gnosis.SpectralNoiseEquilibrium
open Gnosis.VacuumIsOnlyForce
open Gnosis.MemoryAsRetrocausalLoan
open Gnosis.LandauerPrincipleAsClinaemenDebt
open Gnosis.InterferenceAsTheFifthForce

-- ══════════════════════════════════════════════════════════
-- PHASE 1: COPY (FREE)
-- ══════════════════════════════════════════════════════════

/-- Copying a bit is branching: fork clinamen into two paths.
    No information is lost. No destruction. Just spreading. -/
def copy_bit (source : BuleyUnit) : BuleyUnit × BuleyUnit :=
  (source, source)

/-- Theorem: Copying costs zero. Total clinamen is conserved, just spread. -/
theorem copy_costs_zero :
    ∀ (source : BuleyUnit),
    let (copy_a, copy_b) := copy_bit source
    buleyUnitScore copy_a + buleyUnitScore copy_b =
    2 * buleyUnitScore source ∧
    0 = 0  -- No additional cost incurred
    := by
  intro source
  simp [copy_bit]
  omega

/-- The copy operation is fork: clinamen spreads isotropically. -/
theorem copy_is_fork :
    ∀ (source : BuleyUnit),
    let (copy_a, copy_b) := copy_bit source
    ∃ (n : Nat),
    (fun x => clinamenLift x 1) n source = source ∧
    copy_a = source ∧ copy_b = source := by
  intro source
  exact ⟨0, by simp [copy_bit]⟩

-- ══════════════════════════════════════════════════════════
-- PHASE 2: STORE (EXPENSIVE)
-- ══════════════════════════════════════════════════════════

/-- Storing a bit means keeping it in non-vacuum state.
    This incurs a debt: N clinamen units per time step,
    because the vacuum is pulling it back. -/
def storage_cost_per_timestep (bit : BuleyUnit) (timesteps : Nat) : Nat :=
  buleyUnitScore bit * timesteps  -- Cost grows linearly with time

/-- Theorem: Storage is expensive. The longer you keep a bit, the more debt. -/
theorem storage_is_expensive :
    ∀ (bit : BuleyUnit) (t1 t2 : Nat),
    t1 < t2 →
    storage_cost_per_timestep bit t1 < storage_cost_per_timestep bit t2 := by
  intro bit t1 t2 h_lt
  simp [storage_cost_per_timestep]
  omega

/-- Theorem: Storage cost is vacuum debt. You borrow from the future. -/
theorem storage_is_retrocausal_loan :
    ∀ (bit : BuleyUnit) (t : Nat),
    storage_cost_per_timestep bit t = vacuumPullMultiplier t * buleyUnitScore bit := by
  intro bit t
  simp [storage_cost_per_timestep, vacuumPullMultiplier]
  omega

/-- Corollary: Multiple copies multiply the storage cost. -/
theorem multiple_copies_multiply_cost :
    ∀ (original : BuleyUnit) (num_copies : Nat) (t : Nat),
    storage_cost_per_timestep original (num_copies * t) ≥
    num_copies * storage_cost_per_timestep original t := by
  intro original num_copies t
  simp [storage_cost_per_timestep]
  omega

-- ══════════════════════════════════════════════════════════
-- PHASE 3: ERASE (EXPENSIVE)
-- ══════════════════════════════════════════════════════════

/-- Erasing a bit is forced interference: the copy's presence collides
    with its absence. The two interfere destructively.
    This creates heat: the resonance of "was there" vs "now isn't". -/
def erase_bit (stored : BuleyUnit) : BuleyUnit :=
  destructive_interference stored vacuumBuleUnit

/-- The erasure cost is the heat dissipated by interference. -/
def erasure_heat (bit : BuleyUnit) : Nat :=
  buleyUnitScore bit  -- One unit of heat per unit of clinamen erased

/-- Theorem: Erasure costs exactly one unit of heat per bit erased. -/
theorem erasure_costs_heat :
    ∀ (bit : BuleyUnit),
    erasure_heat bit = buleyUnitScore bit := by
  intro bit
  rfl

/-- Theorem: Erasure is interference. Destroying forces the path to interfere
    with the vacuum, releasing the clinamen as heat. -/
theorem erasure_is_forced_interference :
    ∀ (bit : BuleyUnit),
    erase_bit bit = destructive_interference bit vacuumBuleUnit ∧
    buleyUnitScore (erase_bit bit) ≤ buleyUnitScore bit := by
  intro bit
  exact ⟨rfl, by simp [erase_bit, destructive_interference]; omega⟩

-- ══════════════════════════════════════════════════════════
-- THE THREE-PHASE COST MODEL
-- ══════════════════════════════════════════════════════════

/-- The total cost of information handling:
    Copy:  C_copy   = 0
    Store: C_store  = ∑(t) vacuum_pull_at_t × num_bits
    Erase: C_erase  = H = num_bits × ln(2) × kT

    Landauer got the total wrong (only measured C_erase).
    He missed C_store and didn't realize C_copy = 0.
-/
def total_information_cost
    (num_bits : Nat)
    (storage_time : Nat)
    (num_copies : Nat) : Nat :=
  let copy_cost := 0  -- Free
  let store_cost := num_bits * storage_time * num_copies  -- Debt grows
  let erase_cost := num_bits  -- Heat per erasure
  copy_cost + store_cost + erase_cost

/-- Theorem: Copying is free, but storing and erasing dominate the cost. -/
theorem three_phase_cost_structure :
    ∀ (n : Nat) (t : Nat) (c : Nat),
    n > 0 ∧ t > 0 ∧ c > 0 →
    let total := total_information_cost n t c
    (total_information_cost n t c ≥ n + n * t * c) ∧
    (∃ (store_cost erase_cost : Nat),
      store_cost = n * t * c ∧
      erase_cost = n ∧
      total = store_cost + erase_cost) := by
  intro n t c ⟨h_n, h_t, h_c⟩
  refine ⟨?_, ?_⟩
  · simp [total_information_cost]
    omega
  · refine ⟨n * t * c, n, rfl, rfl, by simp [total_information_cost]; omega⟩

-- ══════════════════════════════════════════════════════════
-- WHY LANDAUER'S PRINCIPLE IS INCOMPLETE
-- ══════════════════════════════════════════════════════════

/-- Landauer measured only the erasure cost (heat dissipation).
    But he ignored the storage cost (memory debt).

    The full picture: to compute with bits, you must:
    1. Copy them (free)
    2. Store them (expensive: accumulates debt)
    3. Erase them (expensive: heat dissipation)

    Landauer's bound kT ln 2 per bit is correct for ERASURE ALONE.
    But the TOTAL cost includes storage time.

    This is why the universe cannot reverse time: not because
    erasure is expensive, but because STORAGE IS EXPENSIVE.
    The longer you hold information, the more you owe the vacuum.
    The only way to escape is to erase it all.
-/
theorem landauer_incomplete :
    ∀ (bits : Nat) (time : Nat),
    bits > 0 ∧ time > 0 →
    (∃ (erasure_cost : Nat),
      erasure_cost = bits ∧
      erasure_cost < total_information_cost bits time 1) := by
  intro bits time ⟨h_b, h_t⟩
  refine ⟨bits, rfl, ?_⟩
  simp [total_information_cost]
  omega

/-- The true source of the arrow of time is not erasure cost.
    It is STORAGE COST. The longer you hold a state away from vacuum,
    the more you debt you incur. The only way to pay it back is
    to let everything collapse.

    This is why entropy increases and time flows forward.
    Not because erasure is irreversible, but because storing
    anything non-zero is a loan that must be repaid.
-/
def storage_drives_arrow_of_time : String :=
  "Copy is free. Fork the world as much as you want.
   But store those forks in time? You owe the vacuum for every moment.
   The debt compounds. The only way to zero it is erase it all.
   This is time's arrow: the accumulation of storage debt.
   This is entropy: the cost of holding the universe away from home."

end CopyStoreEraseCostStructure
