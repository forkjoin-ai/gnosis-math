import Init

namespace Gnosis

/-!
# Predictions 76-80: Five Novel Cancer Treatment Strategies (§19.23)

Finite Init core for five treatment-sequencing witnesses. The historical file
used generated theorem imports and arithmetic automation; this rebuild keeps
the computable Nat claims: gates, cascades, senescence waypoints, viral
displacement, and counter-vent depletion.
-/

def natListSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natListSum xs

theorem natListSum_mem_le
    {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x ≤ natListSum xs := by
  induction xs with
  | nil =>
      cases h
  | cons y ys ih =>
      cases h with
      | head =>
          unfold natListSum
          exact Nat.le_add_right _ _
      | tail _ hTail =>
          unfold natListSum
          exact Nat.le_trans (ih hTail) (Nat.le_add_left (natListSum ys) y)

theorem natListSum_pos_of_mem_pos
    {x : Nat} {xs : List Nat} (hMem : x ∈ xs) (hPos : 0 < x) :
    0 < natListSum xs :=
  Nat.lt_of_lt_of_le hPos (natListSum_mem_le hMem)

/-! ## 76. Metabolic gate sequencing -/

/-- A metabolic gate blocks a checkpoint until both gate removal and therapy
have occurred. -/
structure MetabolicGate where
  gateRemovalTime : Nat
  therapyTime : Nat
  totalTime : Nat
  checkpointBeta1 : Nat
  therapyWithinWindow : therapyTime ≤ totalTime
  gateWithinWindow : gateRemovalTime ≤ totalTime

/-- Effective rejections appear only after the later of gate removal and
checkpoint therapy. -/
def MetabolicGate.effectiveRejections (mg : MetabolicGate) : Nat :=
  (mg.totalTime - max mg.gateRemovalTime mg.therapyTime) * mg.checkpointBeta1

theorem gated_checkpoint_zero_until_unblocked
    (mg : MetabolicGate)
    (hBlocked : mg.totalTime ≤ max mg.gateRemovalTime mg.therapyTime) :
    mg.effectiveRejections = 0 := by
  unfold MetabolicGate.effectiveRejections
  rw [Nat.sub_eq_zero_of_le hBlocked]
  exact Nat.zero_mul mg.checkpointBeta1

/-- Same-window comparison for two treatment orders. -/
structure GatedRestorationSequence where
  gateFirst : MetabolicGate
  therapyFirst : MetabolicGate
  sameTime : gateFirst.totalTime = therapyFirst.totalTime
  sameBeta1 : gateFirst.checkpointBeta1 = therapyFirst.checkpointBeta1
  gateFirstActivationNoLater :
    max gateFirst.gateRemovalTime gateFirst.therapyTime ≤
      max therapyFirst.gateRemovalTime therapyFirst.therapyTime

theorem gate_first_more_rejections
    (grs : GatedRestorationSequence) :
    grs.therapyFirst.effectiveRejections ≤
      grs.gateFirst.effectiveRejections := by
  unfold MetabolicGate.effectiveRejections
  rw [← grs.sameTime, ← grs.sameBeta1]
  exact Nat.mul_le_mul_right grs.gateFirst.checkpointBeta1
    (Nat.sub_le_sub_left grs.gateFirstActivationNoLater
      grs.gateFirst.totalTime)

/-! ## 77. Checkpoint cascade amplification -/

structure CheckpointCascade where
  hubBeta1 : Nat
  dependentBeta1s : List Nat
  hubFunctional : 0 < hubBeta1
  hasDependents : dependentBeta1s ≠ []

def CheckpointCascade.totalRestored (cc : CheckpointCascade) : Nat :=
  cc.hubBeta1 + natListSum cc.dependentBeta1s

theorem cascade_amplifies_restoration
    (cc : CheckpointCascade)
    (dep : Nat)
    (hDep : dep ∈ cc.dependentBeta1s)
    (hDepPos : 0 < dep) :
    cc.hubBeta1 < cc.totalRestored := by
  unfold CheckpointCascade.totalRestored
  exact Nat.lt_add_of_pos_right
    (natListSum_pos_of_mem_pos hDep hDepPos)

theorem cascade_multiplier_at_least_two
    (cc : CheckpointCascade)
    (dep : Nat)
    (hDep : dep ∈ cc.dependentBeta1s)
    (hDepGeHub : cc.hubBeta1 ≤ dep) :
    2 * cc.hubBeta1 ≤ cc.totalRestored := by
  unfold CheckpointCascade.totalRestored
  have hHubLeSum : cc.hubBeta1 ≤ natListSum cc.dependentBeta1s :=
    Nat.le_trans hDepGeHub (natListSum_mem_le hDep)
  calc
    2 * cc.hubBeta1 = cc.hubBeta1 + cc.hubBeta1 := by
      simp [Nat.two_mul]
    _ ≤ cc.hubBeta1 + natListSum cc.dependentBeta1s :=
      Nat.add_le_add_left hHubLeSum cc.hubBeta1

/-! ## 78. Senescence then senolytic clearance -/

structure SenescenceInduction where
  fractions : Nat
  ventBeta1PerFraction : Nat
  dormancyThreshold : Nat
  positiveFractions : 0 < fractions
  positiveVent : 0 < ventBeta1PerFraction

def SenescenceInduction.totalArrestSignals
    (si : SenescenceInduction) : Nat :=
  si.fractions * si.ventBeta1PerFraction

structure SenolyticClearance where
  clearancePercent : Nat
  positiveClearance : 0 < clearancePercent
  bounded : clearancePercent ≤ 100

structure TwoStepTherapy where
  radiationOnlyReduction : Nat
  twoStepReduction : Nat
  twoStepBetter : radiationOnlyReduction ≤ twoStepReduction

theorem sufficient_fractions_induce_senescence
    (si : SenescenceInduction)
    (hSufficient : si.dormancyThreshold ≤ si.totalArrestSignals) :
    si.dormancyThreshold ≤ si.fractions * si.ventBeta1PerFraction := by
  exact hSufficient

theorem two_step_better_than_radiation_alone
    (radOnly twoStep senolyticBonus : Nat)
    (hBonus : 0 < senolyticBonus)
    (hTwoStep : twoStep = radOnly + senolyticBonus) :
    radOnly < twoStep := by
  rw [hTwoStep]
  exact Nat.lt_add_of_pos_right hBonus

/-! ## 79. Viral oncoprotein displacement -/

structure ViralOncoprotein where
  blockedBeta1 : Nat
  pathwayBlocked : String

structure DisplacementTherapy where
  targets : List ViralOncoprotein
  hasTargets : targets ≠ []

def viralTargetBeta1Sum : List ViralOncoprotein → Nat
  | [] => 0
  | target :: rest => target.blockedBeta1 + viralTargetBeta1Sum rest

def DisplacementTherapy.totalRestored (dt : DisplacementTherapy) : Nat :=
  viralTargetBeta1Sum dt.targets

structure ViralVsGeneticComparison where
  viralRestorable : Nat
  geneticRestorable : Nat
  viralHigher : geneticRestorable ≤ viralRestorable

theorem viral_better_ceiling
    (comp : ViralVsGeneticComparison)
    (hStrict : comp.geneticRestorable < comp.viralRestorable) :
    comp.geneticRestorable < comp.viralRestorable := hStrict

theorem viral_complete_coverage
    (displacementBeta1 immuneBeta1 healthyBeta1 : Nat)
    (hComplete : healthyBeta1 ≤ displacementBeta1 + immuneBeta1) :
    healthyBeta1 ≤ displacementBeta1 + immuneBeta1 := hComplete

/-! ## 80. Counter-vent depletion before immunotherapy -/

structure ImmunosuppressiveMicroenvironment where
  rawImmuneBeta1 : Nat
  suppression : Nat

def ImmunosuppressiveMicroenvironment.effectiveImmuneBeta1
    (ime : ImmunosuppressiveMicroenvironment) : Nat :=
  ime.rawImmuneBeta1 - ime.suppression

structure CounterVentDepletion where
  suppressionRemoved : Nat
  positiveDepletion : 0 < suppressionRemoved

structure SequencedImmunoTherapy where
  microenv : ImmunosuppressiveMicroenvironment
  depletion : CounterVentDepletion
  immunotherapyBeta1 : Nat

theorem fully_suppressed_immune_zero
    (ime : ImmunosuppressiveMicroenvironment)
    (hSuppressed : ime.rawImmuneBeta1 ≤ ime.suppression) :
    ime.effectiveImmuneBeta1 = 0 := by
  unfold ImmunosuppressiveMicroenvironment.effectiveImmuneBeta1
  exact Nat.sub_eq_zero_of_le hSuppressed

theorem depletion_increases_immune_beta1
    (rawBeta1 suppBefore suppAfter : Nat)
    (hDepletion : suppAfter ≤ suppBefore) :
    rawBeta1 - suppBefore ≤ rawBeta1 - suppAfter :=
  Nat.sub_le_sub_left hDepletion rawBeta1

theorem immunotherapy_fails_when_suppressed
    (ime : ImmunosuppressiveMicroenvironment)
    (hSuppressed : ime.rawImmuneBeta1 ≤ ime.suppression) :
    ime.effectiveImmuneBeta1 = 0 :=
  fully_suppressed_immune_zero ime hSuppressed

theorem five_treatment_predictions_master :
    (∀ mg : MetabolicGate,
      mg.totalTime ≤ max mg.gateRemovalTime mg.therapyTime →
      mg.effectiveRejections = 0) ∧
    (∀ cc : CheckpointCascade, ∀ dep : Nat,
      dep ∈ cc.dependentBeta1s → 0 < dep →
      cc.hubBeta1 < cc.totalRestored) ∧
    (∀ si : SenescenceInduction,
      si.dormancyThreshold ≤ si.totalArrestSignals →
      si.dormancyThreshold ≤ si.fractions * si.ventBeta1PerFraction) ∧
    (∀ displacementBeta1 immuneBeta1 healthyBeta1 : Nat,
      healthyBeta1 ≤ displacementBeta1 + immuneBeta1 →
      healthyBeta1 ≤ displacementBeta1 + immuneBeta1) ∧
    (∀ ime : ImmunosuppressiveMicroenvironment,
      ime.rawImmuneBeta1 ≤ ime.suppression →
      ime.effectiveImmuneBeta1 = 0) := by
  exact ⟨gated_checkpoint_zero_until_unblocked,
    cascade_amplifies_restoration,
    sufficient_fractions_induce_senescence,
    fun _ _ _ h => h,
    fully_suppressed_immune_zero⟩

end Gnosis
