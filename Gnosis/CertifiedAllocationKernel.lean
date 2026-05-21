namespace Gnosis

/-!
Finite certified-allocation kernel.

This mirrors the reducer in `open-source/gnosis/src/certified-allocation-kernel.ts`
without importing runtime code into Lean: all state is finite and Nat-valued.
-/

inductive AdmittedObservationZone where
  | topLeft
  | topCenter
  | topRight
  | centerLeft
  | center
  | centerRight
  | bottomLeft
  | bottomCenter
  | bottomRight
deriving DecidableEq, Repr

inductive ObservationZone where
  | admitted : AdmittedObservationZone → ObservationZone
  | unavailable
deriving DecidableEq, Repr

structure NormalizedMilliPoint where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

structure CertifiedObservationFrame where
  gazePoint : Option NormalizedMilliPoint
  zone : ObservationZone
  confidenceScore : Nat
  confidenceFloor : Nat
deriving DecidableEq, Repr

structure CertifiedCalibrationPlan where
  pointCount : Nat
  samplesPerPoint : Nat
  maxAttemptsPerPoint : Nat
deriving DecidableEq, Repr

structure CertifiedCalibrationPointLedger where
  accepted : Nat
  rejected : Nat
  observed : Nat
deriving DecidableEq, Repr

structure CertifiedLoopBudget where
  deadlineMs : Nat
  elapsedMs : Nat
deriving DecidableEq, Repr

inductive CertifiedSafeStateReason where
  | deadlineExceeded
  | notCalibrated
  | observationUnavailable
  | noCandidates
deriving DecidableEq, Repr

inductive CertifiedAllocationDecision where
  | allocate : Nat → CertifiedAllocationDecision
  | safeState : CertifiedSafeStateReason → CertifiedAllocationDecision
deriving DecidableEq, Repr

def observationColumn (point : NormalizedMilliPoint) : Nat :=
  (point.x * 3) / 1000

def observationRow (point : NormalizedMilliPoint) : Nat :=
  (point.y * 3) / 1000

def classifyVisibleZone (point : NormalizedMilliPoint) : AdmittedObservationZone :=
  match observationRow point, observationColumn point with
  | 0, 0 => .topLeft
  | 0, 1 => .topCenter
  | 0, _ => .topRight
  | 1, 0 => .centerLeft
  | 1, 1 => .center
  | 1, _ => .centerRight
  | _, 0 => .bottomLeft
  | _, 1 => .bottomCenter
  | _, _ => .bottomRight

def classifyObservationZone (point : Option NormalizedMilliPoint) : ObservationZone :=
  match point with
  | none => .unavailable
  | some p => .admitted (classifyVisibleZone p)

def confidenceFloorSatisfied (frame : CertifiedObservationFrame) : Prop :=
  frame.zone = .unavailable ∨ frame.confidenceFloor ≤ frame.confidenceScore

def pointDeficit (plan : CertifiedCalibrationPlan) (point : CertifiedCalibrationPointLedger) : Nat :=
  plan.samplesPerPoint - point.accepted

def requiredSamples (plan : CertifiedCalibrationPlan) : Nat :=
  plan.pointCount * plan.samplesPerPoint

def acceptedSampleCount : List CertifiedCalibrationPointLedger → Nat
  | [] => 0
  | point :: points => point.accepted + acceptedSampleCount points

def rejectedSampleCount : List CertifiedCalibrationPointLedger → Nat
  | [] => 0
  | point :: points => point.rejected + rejectedSampleCount points

def observedSampleCount : List CertifiedCalibrationPointLedger → Nat
  | [] => 0
  | point :: points => point.observed + observedSampleCount points

def calibrationDeficit (plan : CertifiedCalibrationPlan) (points : List CertifiedCalibrationPointLedger) : Nat :=
  requiredSamples plan - acceptedSampleCount points

def pointObservationConserved (point : CertifiedCalibrationPointLedger) : Prop :=
  point.observed = point.accepted + point.rejected

def calibrationObservationConserved : List CertifiedCalibrationPointLedger → Prop
  | [] => True
  | point :: points => pointObservationConserved point ∧ calibrationObservationConserved points

def pointComplete (plan : CertifiedCalibrationPlan) (point : CertifiedCalibrationPointLedger) : Prop :=
  pointDeficit plan point = 0

def pointExhausted (plan : CertifiedCalibrationPlan) (point : CertifiedCalibrationPointLedger) : Prop :=
  plan.maxAttemptsPerPoint ≤ point.observed ∧ 0 < pointDeficit plan point

def pointTerminal (plan : CertifiedCalibrationPlan) (point : CertifiedCalibrationPointLedger) : Prop :=
  pointComplete plan point ∨ pointExhausted plan point

def calibrationTerminated (plan : CertifiedCalibrationPlan) : List CertifiedCalibrationPointLedger → Prop
  | [] => True
  | point :: points => pointTerminal plan point ∧ calibrationTerminated plan points

def pointTerminalBool (plan : CertifiedCalibrationPlan) (point : CertifiedCalibrationPointLedger) : Bool :=
  decide (pointDeficit plan point = 0) ||
    (decide (plan.maxAttemptsPerPoint ≤ point.observed) &&
      decide (0 < pointDeficit plan point))

def calibrationTerminatedBool (plan : CertifiedCalibrationPlan) : List CertifiedCalibrationPointLedger → Bool
  | [] => true
  | point :: points => pointTerminalBool plan point && calibrationTerminatedBool plan points

def calibrationReady
    (plan : CertifiedCalibrationPlan)
    (points : List CertifiedCalibrationPointLedger)
    (modelSolved : Bool) : Bool :=
  calibrationTerminatedBool plan points &&
    decide (calibrationDeficit plan points = 0) &&
    modelSolved

def withinBudget (budget : CertifiedLoopBudget) : Bool :=
  decide (budget.elapsedMs ≤ budget.deadlineMs)

def canonicalCandidateId? : List Nat → Option Nat
  | [] => none
  | candidate :: candidates => some (candidates.foldl Nat.min candidate)

def certifiedAllocationStep
    (plan : CertifiedCalibrationPlan)
    (points : List CertifiedCalibrationPointLedger)
    (modelSolved : Bool)
    (frame : CertifiedObservationFrame)
    (candidateIds : List Nat)
    (budget : CertifiedLoopBudget) : CertifiedAllocationDecision :=
  if withinBudget budget then
    if calibrationReady plan points modelSolved then
      match frame.zone with
      | .unavailable => .safeState .observationUnavailable
      | .admitted _ =>
          match canonicalCandidateId? candidateIds with
          | none => .safeState .noCandidates
          | some candidate => .allocate candidate
    else
      .safeState .notCalibrated
  else
    .safeState .deadlineExceeded

theorem certified_allocation_confidence_floor
    (frame : CertifiedObservationFrame)
    (_hVisible : frame.zone ≠ .unavailable)
    (hFloor : frame.confidenceFloor ≤ frame.confidenceScore) :
    confidenceFloorSatisfied frame := by
  exact Or.inr hFloor

theorem certified_allocation_calibration_deficit
    (plan : CertifiedCalibrationPlan)
    (points : List CertifiedCalibrationPointLedger) :
    calibrationDeficit plan points = requiredSamples plan - acceptedSampleCount points := rfl

theorem certified_allocation_calibration_conservation :
    ∀ points : List CertifiedCalibrationPointLedger,
      calibrationObservationConserved points →
      observedSampleCount points = acceptedSampleCount points + rejectedSampleCount points
  | [], _ => rfl
  | point :: points, h => by
      rcases h with ⟨hPoint, hTail⟩
      unfold pointObservationConserved at hPoint
      simp [observedSampleCount, acceptedSampleCount, rejectedSampleCount]
      rw [hPoint]
      rw [certified_allocation_calibration_conservation points hTail]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem certified_allocation_sharp_admission
    (point : Option NormalizedMilliPoint) :
    classifyObservationZone point = .unavailable ∨
      ∃ zone : AdmittedObservationZone, classifyObservationZone point = .admitted zone := by
  cases point with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨classifyVisibleZone p, rfl⟩

theorem certified_allocation_finite_termination
    (plan : CertifiedCalibrationPlan)
    (points : List CertifiedCalibrationPointLedger)
    (h : ∀ point ∈ points, pointTerminal plan point) :
    calibrationTerminated plan points := by
  induction points with
  | nil => trivial
  | cons point points ih =>
      exact ⟨h point (by simp), ih (by intro tail hTail; exact h tail (by simp [hTail]))⟩

theorem certified_allocation_deadline_failure
    (plan : CertifiedCalibrationPlan)
    (points : List CertifiedCalibrationPointLedger)
    (modelSolved : Bool)
    (frame : CertifiedObservationFrame)
    (candidateIds : List Nat)
    (budget : CertifiedLoopBudget)
    (hLate : budget.deadlineMs < budget.elapsedMs) :
    certifiedAllocationStep plan points modelSolved frame candidateIds budget =
      .safeState .deadlineExceeded := by
  unfold certifiedAllocationStep withinBudget
  simp [Nat.not_le_of_gt hLate]

theorem certified_allocation_loop_progress_or_explicit_failure
    (plan : CertifiedCalibrationPlan)
    (points : List CertifiedCalibrationPointLedger)
    (modelSolved : Bool)
    (frame : CertifiedObservationFrame)
    (candidateIds : List Nat)
    (budget : CertifiedLoopBudget) :
    (∃ candidate, certifiedAllocationStep plan points modelSolved frame candidateIds budget =
      .allocate candidate) ∨
    (∃ reason, certifiedAllocationStep plan points modelSolved frame candidateIds budget =
      .safeState reason) := by
  unfold certifiedAllocationStep
  split
  · split
    · cases frame.zone with
      | unavailable => exact Or.inr ⟨.observationUnavailable, rfl⟩
      | admitted zone =>
          cases hCandidate : canonicalCandidateId? candidateIds with
          | none =>
              exact Or.inr ⟨.noCandidates, by simp⟩
          | some candidate =>
              exact Or.inl ⟨candidate, by simp⟩
    · exact Or.inr ⟨.notCalibrated, rfl⟩
  · exact Or.inr ⟨.deadlineExceeded, rfl⟩

end Gnosis
