import Init

/-!
# Juggling Orbit

Finite orbit-control witnesses for the juggling reducer MCP rows. The file
restores the historical `ForkRaceFoldTheorems` namespace used by the ledger.
-/

namespace ForkRaceFoldTheorems

inductive JugglingHand where
  | left
  | right
deriving DecidableEq, Repr

structure ThrowSignal where
  id : Nat
  beat : Nat
  fromHand : JugglingHand
  catchBeat : Nat
  catchHand : JugglingHand
deriving DecidableEq, Repr

structure CanonicalTransition where
  fromThrowId : Nat
  toThrowId? : Option Nat
  catchBeat : Nat
  catchHand : JugglingHand
deriving DecidableEq, Repr

structure ClosedOrbitWitness where
  members : List Nat
  hNonempty : members ≠ []
  successor : Nat → Nat
  hSuccessorClosed : ∀ id, id ∈ members → successor id ∈ members

structure AsymmetricMultiplexWitness where
  beat : Nat
  hand : JugglingHand
  outgoingCount : Nat
  angleRangeDeg : Nat
  speedRatioMilli : Nat
  hMultiplex : 2 ≤ outgoingCount
  hVariation : 0 < angleRangeDeg ∨ 1000 < speedRatioMilli
deriving Repr

structure MachineOnlyThresholds where
  multiplex : Nat
  angleDeg : Nat
  speedRatioMilli : Nat
deriving Repr

structure MachineOnlySourceWitness where
  beat : Nat
  hand : JugglingHand
  outgoingCount : Nat
  angleRangeDeg : Nat
  speedRatioMilli : Nat
  thresholds : MachineOnlyThresholds
  hMultiplex : thresholds.multiplex ≤ outgoingCount
  hSeparation : thresholds.angleDeg ≤ angleRangeDeg ∨
    thresholds.speedRatioMilli ≤ speedRatioMilli
deriving Repr

def conservationMismatch (incoming outgoing : Nat) : Nat :=
  outgoing - incoming

theorem juggling_orbit_transition_deterministic
    (transition : CanonicalTransition)
    (candidateA candidateB : Nat)
    (hA : transition.toThrowId? = some candidateA)
    (hB : transition.toThrowId? = some candidateB) :
    candidateA = candidateB := by
  rw [hA] at hB
  injection hB

theorem juggling_orbit_decomposition_fold
    (orbit : ClosedOrbitWitness) :
    orbit.members ≠ [] ∧
    ∀ id, id ∈ orbit.members → orbit.successor id ∈ orbit.members :=
  ⟨orbit.hNonempty, orbit.hSuccessorClosed⟩

theorem juggling_asymmetric_multiplex_witness
    (witness : AsymmetricMultiplexWitness) :
    2 ≤ witness.outgoingCount ∧
    (0 < witness.angleRangeDeg ∨ 1000 < witness.speedRatioMilli) :=
  ⟨witness.hMultiplex, witness.hVariation⟩

theorem juggling_conservation_per_beat_hand
    (incoming outgoing : Nat)
    (hBalanced : incoming = outgoing) :
    conservationMismatch incoming outgoing = 0 := by
  unfold conservationMismatch
  rw [hBalanced]
  exact Nat.sub_self outgoing

theorem juggling_machine_only_candidate_boundary
    (witness : MachineOnlySourceWitness) :
    witness.thresholds.multiplex ≤ witness.outgoingCount ∧
    (witness.thresholds.angleDeg ≤ witness.angleRangeDeg ∨
      witness.thresholds.speedRatioMilli ≤ witness.speedRatioMilli) :=
  ⟨witness.hMultiplex, witness.hSeparation⟩

theorem open_orbit_does_not_guarantee_sustainability
    (openMember : Nat) :
    ¬ (∀ transition : CanonicalTransition,
        transition.fromThrowId = openMember →
        ∃ nextId, transition.toThrowId? = some nextId) := by
  intro hAll
  let transition : CanonicalTransition :=
    { fromThrowId := openMember
      toThrowId? := none
      catchBeat := 0
      catchHand := JugglingHand.left }
  rcases hAll transition rfl with ⟨nextId, hNext⟩
  cases hNext

theorem conservation_balance_does_not_force_closed_orbit :
    ¬ (∀ transition : CanonicalTransition,
        conservationMismatch 0 0 = 0 →
        ∃ nextId, transition.toThrowId? = some nextId) := by
  intro hAll
  let transition : CanonicalTransition :=
    { fromThrowId := 0
      toThrowId? := none
      catchBeat := 0
      catchHand := JugglingHand.left }
  have hBalanced : conservationMismatch 0 0 = 0 := by decide
  rcases hAll transition hBalanced with ⟨nextId, hNext⟩
  cases hNext

end ForkRaceFoldTheorems
