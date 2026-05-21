import Gnosis.ArnoldCatMapOrder5
import Gnosis.FailureFamilies
import Gnosis.FanoIncidence
import Gnosis.GodFormula
import Gnosis.InftyOperads
import Gnosis.ProvisionalCertificate
import Gnosis.QuarkPersonality
import Gnosis.StepwiseAnalysisFramework

/-!
# Fork Face Fold

Finite Lean backing for the tabletop game sketch.  The module does not claim
that the math proves the game is fun; it pins the rules to the same bounded
objects used by the Gnosis ledger:

* two d5 rolls as a coordinate on `(Z/5)^2`;
* Arnold's cat map as the race motion;
* `godWeight` as the branch score;
* branch isolation as the clean-failure condition;
* five walkers and five K4 fold states as card/variant faces;
* die faces `1..5` as fork/race/fold/vent/sliver;
* the seven visible Triton/Fano states as the 3D minimum-Grassmannian variant;
* provisional certificate statuses for the Anti-Certificate variant.
-/

namespace Gnosis
namespace ForkFaceFoldGame

/-! ## Components -/

/-- A physical d5 face after normalization into `0..4`. -/
def d5Face (rawFace : Nat) : Nat := rawFace % 5

/-- The five operation faces printed on the d5. -/
abbrev OperationFace := StepwiseAnalysisFramework.FrfStep

/-- Human-facing d5 labels: `1=fork`, `2=race`, `3=fold`, `4=vent`,
    `5=sliver`. Other natural inputs normalize modulo five. -/
def operationFaceOfDieLabel (label : Nat) : OperationFace :=
  match label % 5 with
  | 1 => .fork
  | 2 => .race
  | 3 => .fold
  | 4 => .vent
  | _ => .sliver

theorem die_label_one_is_fork :
    operationFaceOfDieLabel 1 = .fork := rfl

theorem die_label_two_is_race :
    operationFaceOfDieLabel 2 = .race := rfl

theorem die_label_three_is_fold :
    operationFaceOfDieLabel 3 = .fold := rfl

theorem die_label_four_is_vent :
    operationFaceOfDieLabel 4 = .vent := rfl

theorem die_label_five_is_sliver :
    operationFaceOfDieLabel 5 = .sliver := rfl

theorem operation_faces_cycle_after_five :
    StepwiseAnalysisFramework.phaseSucc
      (StepwiseAnalysisFramework.phaseSucc
        (StepwiseAnalysisFramework.phaseSucc
          (StepwiseAnalysisFramework.phaseSucc
            (StepwiseAnalysisFramework.phaseSucc .fork)))) = .fork :=
  StepwiseAnalysisFramework.phase_succ_five_cycle

/-- The two dice are read as a coordinate on the finite 5 by 5 torus. -/
abbrev D5Coordinate := Nat × Nat

/-- Normalize an arbitrary coordinate into `(Z/5)^2`. -/
def normalizeCoordinate (p : D5Coordinate) : D5Coordinate :=
  (p.1 % 5, p.2 % 5)

/-- Race motion: Arnold's cat map on `(Z/5)^2`. -/
def raceStep (p : D5Coordinate) : D5Coordinate :=
  ArnoldCatMapOrder5.CatMap 5 p

/-- Repeated race motion. -/
def raceAfter (steps : Nat) (p : D5Coordinate) : D5Coordinate :=
  ArnoldCatMapOrder5.catMapIter 5 steps p

/-- The 25 playable board coordinates. -/
def boardCoordinates : List D5Coordinate :=
  ArnoldCatMapOrder5.allPointsMod5

theorem board_has_twenty_five_spaces :
    boardCoordinates.length = 25 :=
  ArnoldCatMapOrder5.allPointsMod5_length

/-- The cat-map return objective: after exactly 10 steps every board point is fixed. -/
theorem cat_map_return_after_ten :
    boardCoordinates.all (fun p => raceAfter 10 p == p) = true :=
  ArnoldCatMapOrder5.catMap_pow_10_id_mod_5

/-- A one-step race from `(1,0)` fails to return, keeping the 10-step win legible. -/
theorem one_step_is_not_cat_map_return :
    raceAfter 1 (1, 0) ≠ (1, 0) :=
  ArnoldCatMapOrder5.catMap_pow_1_not_id_mod_5

/-- A two-step race from `(1,0)` also fails to return. -/
theorem two_steps_are_not_cat_map_return :
    raceAfter 2 (1, 0) ≠ (1, 0) :=
  ArnoldCatMapOrder5.catMap_pow_2_not_id_mod_5

/-- A five-step race from `(1,0)` also fails to return. -/
theorem five_steps_are_not_cat_map_return :
    raceAfter 5 (1, 0) ≠ (1, 0) :=
  ArnoldCatMapOrder5.catMap_pow_5_not_id_mod_5

/-! ## Fork/Race/Fold state -/

/-- The playable triptych: failure is a state, not elimination. -/
inductive BranchState where
  | refusal
  | ground
  | closure
  deriving DecidableEq, Repr

/-- One recovery step along `Refusal -> Ground -> Closure`. -/
def recoveryStep : BranchState -> BranchState
  | .refusal => .ground
  | .ground => .closure
  | .closure => .closure

theorem refusal_recovers_to_ground :
    recoveryStep .refusal = .ground := rfl

theorem ground_recovers_to_closure :
    recoveryStep .ground = .closure := rfl

theorem two_step_recovery_closes_refusal :
    recoveryStep (recoveryStep .refusal) = .closure := rfl

/-- The card suits are the five QuarkPersonality walkers. -/
abbrev WalkerSuit := QuarkPersonality.Walker

/-- The five walker suits support the 45-card deck's repeating face language. -/
theorem walker_suit_count_is_five :
    QuarkPersonality.allWalkers.length = 5 :=
  QuarkPersonality.five_walkers

/-- The 10 pairwise walker channels provide the optional advanced interaction grid. -/
theorem walker_pair_channels_are_ten :
    5 * 4 / 2 = 10 :=
  QuarkPersonality.ten_from_five

/-! ## Scoring -/

/-- Default branch budget for the tabletop rules. -/
def defaultBranchBudget : Nat := 4

/-- Branch score: `R - min(v,R) + 1`, shared with the Gnosis GodFormula surface. -/
def branchScore (budget rejections : Nat) : Nat :=
  godWeight budget rejections

/-- Default score for the normal game budget. -/
def defaultBranchScore (rejections : Nat) : Nat :=
  branchScore defaultBranchBudget rejections

theorem branch_score_is_always_positive (budget rejections : Nat) :
    1 ≤ branchScore budget rejections :=
  godWeight_pos budget rejections

theorem branch_score_never_exceeds_ceiling (budget rejections : Nat) :
    branchScore budget rejections ≤ budget + 1 :=
  godWeight_le_succ budget rejections

theorem default_branch_score_between_one_and_five (rejections : Nat) :
    1 ≤ defaultBranchScore rejections ∧ defaultBranchScore rejections ≤ 5 := by
  constructor
  · exact branch_score_is_always_positive defaultBranchBudget rejections
  · exact branch_score_never_exceeds_ceiling defaultBranchBudget rejections

theorem zero_rejection_scores_five :
    defaultBranchScore 0 = 5 :=
  godWeight_ceiling defaultBranchBudget

theorem full_rejection_scores_one :
    defaultBranchScore defaultBranchBudget = 1 :=
  godWeight_floor defaultBranchBudget

theorem more_rejection_cannot_raise_score
    (v₁ v₂ : Nat) (h₁ : v₁ ≤ defaultBranchBudget) (h₂ : v₂ ≤ defaultBranchBudget)
    (h : v₁ ≤ v₂) :
    defaultBranchScore v₂ ≤ defaultBranchScore v₁ :=
  godWeight_antitone defaultBranchBudget v₁ v₂ h₁ h₂ h

/-! ## Perfect failure -/

/-- A clean-failure certificate for a branch set before and after a fold. -/
structure PerfectFailureCertificate where
  before : List BranchSnapshot
  after : List BranchSnapshot
  branchIsolating : BranchIsolating before after

/-- Perfect failure has zero repair debt by the existing branch-isolation theorem. -/
theorem perfect_failure_has_zero_repair_debt (c : PerfectFailureCertificate) :
    repairDebt c.before c.after = 0 :=
  branch_isolating_has_zero_repair_debt c.before c.after c.branchIsolating

/-- Perfect failure blocks contagious mutation of surviving outputs. -/
theorem perfect_failure_blocks_contagion (c : PerfectFailureCertificate) :
    ¬ ContagiousFailure c.before c.after :=
  branch_isolating_blocks_contagion c.before c.after c.branchIsolating

/-- Any contagious failure forces repair debt, so it cannot be a perfect failure. -/
theorem contagious_failure_is_not_perfect
    (before after : List BranchSnapshot)
    (h : ContagiousFailure before after) :
    0 < repairDebt before after :=
  contagious_failure_forces_repair_debt before after h

/-! ## Pentagon Fold variant -/

/-- The five Stasheff K4 fold faces used by the light variant. -/
abbrev FoldFace := InftyOperads.Paren4

/-- The five fold faces in their pentagon order. -/
def pentagonFoldFaces : List FoldFace :=
  InftyOperads.K4_cycle

theorem pentagon_fold_has_five_faces :
    pentagonFoldFaces.length = 5 :=
  InftyOperads.K4_cycle_length

theorem pentagon_boundary_closes :
    InftyOperads.K4_boundary2 ⟨true⟩ = ⟨true, true, true, true, true⟩ :=
  InftyOperads.K4_pentagon_closes

theorem pentagon_boundary_has_no_boundary :
    InftyOperads.K4_boundary1 (InftyOperads.K4_boundary2 ⟨true⟩) =
      InftyOperads.PK4_C0.zero :=
  InftyOperads.K4_boundary_squared_zero

/-! ## 3D seven-point Fano variant -/

/-- The 3D variant uses the seven visible nonzero states of the Triton/Fano carrier. -/
abbrev FanoGamePoint := FanoIncidence.FanoPoint

/-- Explicit seven-point carrier for a physical 3D minimum-Grassmannian board. -/
def fanoGamePoints : List FanoGamePoint :=
  [ .b001, .b010, .b011, .b100, .b101, .b110, .b111 ]

theorem fano_game_has_seven_points :
    fanoGamePoints.length = 7 := rfl

/-- In the Fano variant, racing two distinct points closes the third point on the line. -/
def fanoRaceCompletion (a b : FanoGamePoint) : FanoGamePoint :=
  FanoIncidence.completePair a b

theorem fano_race_completion_is_third_point
    (a b : FanoGamePoint) (hab : a ≠ b) :
    fanoRaceCompletion a b ≠ a ∧
    fanoRaceCompletion a b ≠ b ∧
    FanoIncidence.fanoLine a b (fanoRaceCompletion a b) :=
  let h := FanoIncidence.distinct_pair_unique_completion a b hab
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- A completed Fano line has zero XOR parity in the 3D carrier. -/
theorem fano_race_completion_zero_parity
    (a b : FanoGamePoint) (hab : a ≠ b) :
    FanoIncidence.collide
      (FanoIncidence.collide a.state b.state)
      (fanoRaceCompletion a b).state =
    FanoIncidence.godPosition :=
  FanoIncidence.completePair_xor_parity_zero a b hab

/-! ## Interesting-game criterion -/

/-- A bounded design profile for judging whether a tabletop game has enough
structure to be worth iterating. The fields are intentionally finite and
playtest-facing, not psychological absolutes. -/
structure GameInterestProfile where
  actionFaces : Nat
  uncertaintyStates : Nat
  failureRecoverySteps : Nat
  scoreCeiling : Nat
  closureTarget : Nat
  hasCleanFailureBonus : Bool
  hasAlternateWin : Bool
  deriving DecidableEq, Repr

/-- A game is interesting when it has more than one meaningful action, more
than one uncertainty state, recoverable failure, bounded scores, a nontrivial
closure target, and at least one payoff route for clean failure or alternate
closure. -/
def InterestingGame (profile : GameInterestProfile) : Prop :=
  1 < profile.actionFaces ∧
    1 < profile.uncertaintyStates ∧
    0 < profile.failureRecoverySteps ∧
    profile.scoreCeiling ≤ 5 ∧
    profile.scoreCeiling < profile.closureTarget ∧
    (profile.hasCleanFailureBonus = true ∨ profile.hasAlternateWin = true)

/-- A five-bit readout for iterative design work. Each bit is one criterion
that can be improved independently by a future rules revision. -/
structure InterestBits where
  meaningfulChoice : Bool
  nontrivialUncertainty : Bool
  recoverableFailure : Bool
  boundedScoring : Bool
  multipleClosureRoutes : Bool
  deriving DecidableEq, Repr

def boolBit : Bool -> Nat
  | true => 1
  | false => 0

def interestBits (profile : GameInterestProfile) : InterestBits where
  meaningfulChoice := decide (1 < profile.actionFaces)
  nontrivialUncertainty := decide (1 < profile.uncertaintyStates)
  recoverableFailure := decide (0 < profile.failureRecoverySteps)
  boundedScoring := decide (profile.scoreCeiling ≤ 5 ∧ profile.scoreCeiling < profile.closureTarget)
  multipleClosureRoutes := profile.hasCleanFailureBonus || profile.hasAlternateWin

/-- Score a completed five-bit interest readout. -/
def interestScoreFromBits (bits : InterestBits) : Nat :=
  boolBit bits.meaningfulChoice +
    boolBit bits.nontrivialUncertainty +
    boolBit bits.recoverableFailure +
    boolBit bits.boundedScoring +
    boolBit bits.multipleClosureRoutes

/-- Interest score ranges from 0 to 5. The target is not "maximum fun";
it is the finite design checklist's full satisfaction. -/
def interestScore (profile : GameInterestProfile) : Nat :=
  interestScoreFromBits (interestBits profile)

theorem interest_score_from_bits_le_five (bits : InterestBits) :
    interestScoreFromBits bits ≤ 5 := by
  cases bits with
  | mk meaningfulChoice nontrivialUncertainty recoverableFailure boundedScoring multipleClosureRoutes =>
      cases meaningfulChoice <;>
        cases nontrivialUncertainty <;>
        cases recoverableFailure <;>
        cases boundedScoring <;>
        cases multipleClosureRoutes <;>
        decide

theorem interest_score_le_five (profile : GameInterestProfile) :
    interestScore profile ≤ 5 :=
  interest_score_from_bits_le_five (interestBits profile)

theorem interesting_game_interest_score_eq_five
    (profile : GameInterestProfile) (h : InterestingGame profile) :
    interestScore profile = 5 := by
  unfold InterestingGame at h
  rcases h with ⟨hChoice, hUncertainty, hRecovery, hCeiling, hClosure, hRoutes⟩
  unfold interestScore interestScoreFromBits interestBits boolBit
  rw [decide_eq_true hChoice]
  rw [decide_eq_true hUncertainty]
  rw [decide_eq_true hRecovery]
  rw [decide_eq_true ⟨hCeiling, hClosure⟩]
  rcases hRoutes with hClean | hAlt
  · rw [hClean]
    cases profile.hasAlternateWin <;> decide
  · rw [hAlt]
    cases profile.hasCleanFailureBonus <;> decide

def forkFaceFoldInterestProfile : GameInterestProfile where
  actionFaces := 5
  uncertaintyStates := boardCoordinates.length
  failureRecoverySteps := 2
  scoreCeiling := 5
  closureTarget := 12
  hasCleanFailureBonus := true
  hasAlternateWin := true

theorem fork_face_fold_is_interesting :
    InterestingGame forkFaceFoldInterestProfile := by
  unfold InterestingGame forkFaceFoldInterestProfile
  decide

theorem fork_face_fold_interest_score_optimal :
    interestScore forkFaceFoldInterestProfile = 5 :=
  interesting_game_interest_score_eq_five
    forkFaceFoldInterestProfile
    fork_face_fold_is_interesting

/-- A design refinement is progress when it does not lower the finite interest
score. This is the local iteration hook for future playtest variants. -/
def InterestNondecreasing (before after : GameInterestProfile) : Prop :=
  interestScore before ≤ interestScore after

theorem interest_refinement_is_bounded_by_five
    (before after : GameInterestProfile)
    (_h : InterestNondecreasing before after) :
    interestScore after ≤ 5 :=
  interest_score_le_five after

theorem fork_face_fold_cannot_improve_interest_score
    (candidate : GameInterestProfile)
    (h : InterestNondecreasing forkFaceFoldInterestProfile candidate) :
    interestScore candidate = 5 := by
  have hUpper := interest_score_le_five candidate
  have hLower : 5 ≤ interestScore candidate := by
    rw [← fork_face_fold_interest_score_optimal]
    exact h
  exact Nat.le_antisymm hUpper hLower

/-! ## Dynamic adaptation toward interest optimality -/

/-- Runtime observations a table can record after a round. Each field is a
finite proxy for a weak interest dimension: stalled choices, repeated states,
unrecovered failures, scoring spikes, and single-route endings. -/
structure PlayTelemetry where
  decisionStalls : Nat
  repeatedStates : Nat
  unrecoveredFailures : Nat
  scoreSpikes : Nat
  singleRouteClosures : Nat
  deriving DecidableEq, Repr

/-- Total pressure seen by the adaptive rules. Kept as a transparent Nat so
future variants can use it for thresholds without changing the telemetry wire. -/
def telemetryPressure (telemetry : PlayTelemetry) : Nat :=
  telemetry.decisionStalls +
    telemetry.repeatedStates +
    telemetry.unrecoveredFailures +
    telemetry.scoreSpikes +
    telemetry.singleRouteClosures

/-- One adaptive pass after a played round. It preserves the old profile as
input, but guarantees the next profile has enough action space, uncertainty,
failure recovery, bounded scoring, and multiple closure routes. Telemetry adds
extra aperture where the table observed pressure. -/
def adaptInterestProfile
    (profile : GameInterestProfile)
    (telemetry : PlayTelemetry) : GameInterestProfile where
  actionFaces := profile.actionFaces + telemetry.decisionStalls + 2
  uncertaintyStates := profile.uncertaintyStates + telemetry.repeatedStates + 2
  failureRecoverySteps := profile.failureRecoverySteps + telemetry.unrecoveredFailures + 1
  scoreCeiling := 5
  closureTarget := profile.closureTarget + telemetry.scoreSpikes + 6
  hasCleanFailureBonus := true
  hasAlternateWin := profile.hasAlternateWin || decide (0 < telemetry.singleRouteClosures)

theorem adapted_profile_has_meaningful_choice
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    1 < (adaptInterestProfile profile telemetry).actionFaces := by
  unfold adaptInterestProfile
  exact Nat.lt_of_lt_of_le (by decide : 1 < 2)
    (Nat.le_trans (Nat.le_add_left 2 (profile.actionFaces + telemetry.decisionStalls))
      (Nat.le_refl _))

theorem adapted_profile_has_uncertainty
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    1 < (adaptInterestProfile profile telemetry).uncertaintyStates := by
  unfold adaptInterestProfile
  exact Nat.lt_of_lt_of_le (by decide : 1 < 2)
    (Nat.le_trans (Nat.le_add_left 2 (profile.uncertaintyStates + telemetry.repeatedStates))
      (Nat.le_refl _))

theorem adapted_profile_has_recovery
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    0 < (adaptInterestProfile profile telemetry).failureRecoverySteps := by
  unfold adaptInterestProfile
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1)
    (Nat.le_trans
      (Nat.le_add_left 1 (profile.failureRecoverySteps + telemetry.unrecoveredFailures))
      (Nat.le_refl _))

theorem adapted_profile_has_bounded_scoring
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    (adaptInterestProfile profile telemetry).scoreCeiling ≤ 5 ∧
      (adaptInterestProfile profile telemetry).scoreCeiling <
        (adaptInterestProfile profile telemetry).closureTarget := by
  constructor
  · unfold adaptInterestProfile
    exact Nat.le_refl 5
  · unfold adaptInterestProfile
    exact Nat.lt_of_lt_of_le (by decide : 5 < 6)
      (Nat.le_trans
        (Nat.le_add_left 6 (profile.closureTarget + telemetry.scoreSpikes))
        (Nat.le_refl _))

theorem adapted_profile_has_multiple_routes
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    (adaptInterestProfile profile telemetry).hasCleanFailureBonus = true ∨
      (adaptInterestProfile profile telemetry).hasAlternateWin = true := by
  left
  rfl

theorem adapted_profile_is_interesting
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    InterestingGame (adaptInterestProfile profile telemetry) :=
  ⟨ adapted_profile_has_meaningful_choice profile telemetry
  , adapted_profile_has_uncertainty profile telemetry
  , adapted_profile_has_recovery profile telemetry
  , (adapted_profile_has_bounded_scoring profile telemetry).1
  , (adapted_profile_has_bounded_scoring profile telemetry).2
  , adapted_profile_has_multiple_routes profile telemetry
  ⟩

theorem adapted_profile_interest_score_optimal
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    interestScore (adaptInterestProfile profile telemetry) = 5 :=
  interesting_game_interest_score_eq_five
    (adaptInterestProfile profile telemetry)
    (adapted_profile_is_interesting profile telemetry)

theorem adaptive_pass_is_nondecreasing
    (profile : GameInterestProfile) (telemetry : PlayTelemetry) :
    InterestNondecreasing profile (adaptInterestProfile profile telemetry) := by
  unfold InterestNondecreasing
  rw [adapted_profile_interest_score_optimal profile telemetry]
  exact interest_score_le_five profile

/-! ## Anti-Certificate variant -/

/-- The Anti-Certificate variant uses the same three empirical statuses. -/
abbrev ClaimStatus := ProvisionalCertificate.EmpiricalClaimStatus

/-- A claim with no experiment is vacuous, not scored as a win. -/
theorem untested_claim_is_vacuous :
    ProvisionalCertificate.current_provisional_status
      { model_id := .Llama1B
        hypothesis := "untested game claim"
        witnesses_supporting := []
        witnesses_falsifying := [] } =
      .VacuousNoExperimentSpecified := by
  rfl

/-- One supporting witness and no falsifier keeps a claim alive but provisional. -/
theorem supported_unfalsified_claim_is_not_yet_falsified :
    ProvisionalCertificate.current_provisional_status
      { model_id := .Qwen0_5B
        hypothesis := "playtest claim survived one table"
        witnesses_supporting := [ProvisionalCertificate.wave_2_qwen_0_5b_supporting_witness]
        witnesses_falsifying := [] } =
      .NotYetFalsified := by
  rfl

/-- One falsifying witness kills the claim at the recorded methodology. -/
theorem falsifying_witness_sets_falsified_status :
    ProvisionalCertificate.current_provisional_status
      { model_id := .QwenCoder7B
        hypothesis := "playtest claim failed"
        witnesses_supporting := []
        witnesses_falsifying := [ProvisionalCertificate.wave_4_qwen_coder_7b_falsifying_witness] } =
      .FalsifiedByMeasurement := by
  rfl

end ForkFaceFoldGame
end Gnosis
