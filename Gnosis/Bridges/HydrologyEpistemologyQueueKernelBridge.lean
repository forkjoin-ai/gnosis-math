namespace Gnosis

/-!
Init-only hydrology/epistemology queue bridge.

`Nat`-valued M/M/1 boundary witness with `arrivalRate < serviceRate`;
geometric ergodicity rate as a `(numerator, denominator)` pair.
-/

structure HydrologySetup where
  precipitation : Nat
  evapotranspiration : Nat
  runoff : Nat
  hRunoffPos : 0 < runoff
  hEq : precipitation = evapotranspiration + runoff

structure EpistemologySetup where
  justifiedBeliefs : Nat
  trueBeliefs : Nat
  gettierCases : Nat
  hGettierPos : 0 < gettierCases
  hEq : justifiedBeliefs + trueBeliefs = gettierCases + 1

structure QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat

def canonicalMM1Boundary_HydrologyEpistemologyQueueKernelBridge (lam mu : Nat) (_h : lam < mu) : QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge :=
  { beta1 := 0, capacity := 1, arrivalRate := lam, serviceRate := mu }

theorem hydrology_runoff_yields_unit_queue_boundary
    (hydro : HydrologySetup) :
    ∃ boundary : QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = hydro.runoff ∧
      boundary.serviceRate = 2 * hydro.runoff + 1 := by
  have h : hydro.runoff < 2 * hydro.runoff + 1 := by omega
  exact ⟨canonicalMM1Boundary_HydrologyEpistemologyQueueKernelBridge hydro.runoff (2 * hydro.runoff + 1) h, rfl, rfl, rfl, rfl⟩

theorem epistemology_gettier_yields_unit_queue_boundary
    (epis : EpistemologySetup) :
    ∃ boundary : QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = epis.gettierCases ∧
      boundary.serviceRate = 2 * epis.gettierCases + 1 := by
  have h : epis.gettierCases < 2 * epis.gettierCases + 1 := by omega
  exact ⟨canonicalMM1Boundary_HydrologyEpistemologyQueueKernelBridge epis.gettierCases (2 * epis.gettierCases + 1) h, rfl, rfl, rfl, rfl⟩

theorem hydrology_epistemology_budget_yields_unit_queue_boundary
    (hydro : HydrologySetup) (epis : EpistemologySetup)
    (_hBudgetBridge : hydro.runoff = epis.gettierCases) :
    ∃ boundary : QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = hydro.runoff ∧
      boundary.serviceRate = 2 * epis.gettierCases + 1 := by
  have h : hydro.runoff < 2 * epis.gettierCases + 1 := by omega
  exact ⟨canonicalMM1Boundary_HydrologyEpistemologyQueueKernelBridge hydro.runoff (2 * epis.gettierCases + 1) h, rfl, rfl, rfl, rfl⟩

theorem hydrology_epistemology_budget_does_not_force_positive_beta1
    (hydro : HydrologySetup) (epis : EpistemologySetup)
    (hBudgetBridge : hydro.runoff = epis.gettierCases) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge,
        boundary.arrivalRate = hydro.runoff →
        boundary.serviceRate = 2 * epis.gettierCases + 1 →
        0 < boundary.beta1) := by
  intro hPositive
  rcases hydrology_epistemology_budget_yields_unit_queue_boundary hydro epis hBudgetBridge with
    ⟨boundary, hBetaZero, _, hArr, hSrv⟩
  have hPos : 0 < boundary.beta1 := hPositive boundary hArr hSrv
  rw [hBetaZero] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem hydrology_epistemology_budget_does_not_force_strict_capacity_growth
    (hydro : HydrologySetup) (epis : EpistemologySetup)
    (hBudgetBridge : hydro.runoff = epis.gettierCases) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat_HydrologyEpistemologyQueueKernelBridge,
        boundary.arrivalRate = hydro.runoff →
        boundary.serviceRate = 2 * epis.gettierCases + 1 →
        1 < boundary.capacity) := by
  intro hGrowth
  rcases hydrology_epistemology_budget_yields_unit_queue_boundary hydro epis hBudgetBridge with
    ⟨boundary, _, hCapacityOne, hArr, hSrv⟩
  have hCap : 1 < boundary.capacity := hGrowth boundary hArr hSrv
  rw [hCapacityOne] at hCap
  exact Nat.lt_irrefl 1 hCap

structure GeometricErgodicityRateNat_HydrologyEpistemologyQueueKernelBridge where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound

theorem hydrology_epistemology_budget_yields_geometric_rate_certificate
    (hydro : HydrologySetup) (epis : EpistemologySetup)
    (_hBudgetBridge : hydro.runoff = epis.gettierCases) :
    ∃ cert : GeometricErgodicityRateNat_HydrologyEpistemologyQueueKernelBridge,
      cert.numerator = 3 ∧ cert.denominator = 4 ∧
      cert.initialBound = hydro.runoff + 1 := by
  refine ⟨{
    numerator := 3, denominator := 4
    initialBound := hydro.runoff + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos _
  }, rfl, rfl, rfl⟩

structure MultiLevelHarrisWitnessNat_HydrologyEpistemologyQueueKernelBridge where
  discreteDriftGap : Nat
  continuousDriftGap : Nat
  hDiscrete : 0 < discreteDriftGap
  hContinuous : 0 < continuousDriftGap

theorem hydrology_epistemology_multilevel_harris_witness
    (hydro : HydrologySetup) (epis : EpistemologySetup)
    (_hBudgetBridge : hydro.runoff = epis.gettierCases) :
    ∃ witness : MultiLevelHarrisWitnessNat_HydrologyEpistemologyQueueKernelBridge,
      witness.discreteDriftGap = hydro.runoff ∧
      witness.continuousDriftGap = epis.gettierCases := by
  exact ⟨{
    discreteDriftGap := hydro.runoff
    continuousDriftGap := epis.gettierCases
    hDiscrete := hydro.hRunoffPos
    hContinuous := epis.hGettierPos
  }, rfl, rfl⟩

end Gnosis
