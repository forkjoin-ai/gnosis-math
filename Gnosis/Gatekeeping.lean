import Init
import Gnosis.GameTheoreticProtocolDeficit

/-
  Gatekeeping.lean
  =================

  Spec-level carrier for *when*, *where*, and *how* gatekeeping is used, plus
  predicates for *effective* vs *ineffective* usage. Numbers are calibration
  knobs (0–100) for downstream runtime / social layers; theorems unpack
  definitions and arithmetic witnesses. Imports `Gnosis.GameTheoreticProtocolDeficit`
  only to align `gateProtocolDeficit` with `protocolDeficit` by `rfl`.

  Alignment with the Nash → Skyrms ladder (see `NashSkyrmsBuleyGodLadder.lean`):
  gatekeeping is primarily a Skyrms phenomenon (convention / collective
  expectation about who may pass), not a single-agent Nash deviation; the
  `GateEpisteme` fields name the epistemic preconditions for convention lock-in.

  Zero `sorry`, zero new `axiom`.

  Onward (throughput / Skyrms–stag linkage): `gateProtocolDeficit` uses the same
  `paths - streams` shape as `Gnosis.protocolDeficit` when `paths = nominalLegitDemand`
  and `streams = legitThroughput`. A toy `StagHuntConvention` maps coordination level
  to metrics so deficit equals unreached mutual-stag capacity on the 0–100 dial.

  Game layer: see `Gnosis.GatekeepingGames` for PD-shaped `IndividualGate` profiles,
  God-formula payoffs, Skyrms convention metrics, and the ladder ordering witness.
-/


namespace Gatekeeping

open Gnosis (protocolDeficit)

/-! ## Where — carrier (what substrate the gate sits on) -/

/-- What is being gated: risk, scarcity, semantics, identity boundary, or attention. -/
inductive GateCarrier : Type where
  | risk
  | scarcity
  | qualitySemantics
  | identityBoundary
  | attention
  deriving DecidableEq, Repr

/-! ## When — interaction and information shape (convention preconditions) -/

/-- `repeated`: repeated game / reputation channel exists.
    `asymmetricInfo`: gatekeeper observes hazards or capacity the seeker does not. -/
structure GateEpisteme where
  repeated : Bool
  asymmetricInfo : Bool
  deriving DecidableEq, Repr

/-! ## How — mechanism style -/

inductive GateStyle : Type where
  /-- Checklist or numeric rule is public and stable. -/
  | publishedThreshold
  /-- Costly signal / credential whose cost tracks hidden type or effort. -/
  | costlySignal
  /-- Human discretion with accountable mandate. -/
  | discretionary
  /-- Rules move, are unpublished, or criteria are post-hoc. -/
  | hiddenCriteria
  deriving DecidableEq, Repr

/-! ## Policy knobs (strictness, transparency, recourse, verified bottleneck) -/

/-- `bottleneck`: verified magnitude of real hazard or scarcity (0 = none on record).
    `strictness`: how hard the gate is to pass (0 loose .. 100 strict).
    `opacity`: inverse transparency (0 fully public .. 100 hiddenCriteria).
    `appealPath`: documented appeal or review exists. -/
structure Gate where
  carrier : GateCarrier
  episteme : GateEpisteme
  style : GateStyle
  strictness : Nat
  opacity : Nat
  appealPath : Bool
  /-- External constraint strength: capacity, safety budget, or audit evidence. -/
  bottleneck : Nat
  deriving Repr

/-! ## Outcomes (normalized rates 0–100) -/

/-- `falseReject`: good seekers or good information wrongly blocked.
    `falseAccept`: bad actors or harmful content wrongly accepted.
    `legitThroughput`: normalized flow of legitimate passage (higher is better). -/
structure GateMetrics where
  falseReject : Nat
  falseAccept : Nat
  legitThroughput : Nat
  deriving Repr

/-! ## Calibration constants (ledger-level; tune in calibration layer) -/

/-- Above this bottleneck, false accepts must stay low to count as effective. -/
def hazardThreshold : Nat := 50

/-- Maximum tolerable false-accept rate when hazard is active. -/
def maxFalseAcceptUnderHazard : Nat := 15

/-- Loose cap on false rejects for “effective” usage. -/
def maxFalseRejectEffective : Nat := 55

/-- Tighter cap when an appeal path exists (procedural justice witness). -/
def maxFalseRejectWithAppeal : Nat := 40

/-- Strictness at or above this with zero bottleneck witnesses rent-shaped pressure. -/
def rentStrictnessFloor : Nat := 40

/-- False-reject pain level that is hard to justify without a bottleneck. -/
def falseRejectPain : Nat := 60

/-- Failure to contain hazard: false accepts above this under active bottleneck. -/
def failedContainmentFalseAccept : Nat := 35

/-- Opacity level treated as “high” absent other fixes. -/
def highOpacity : Nat := 70

/-- Minimum legit throughput for a “responsive” effective witness (calibration). -/
def minLegitThroughputEffective : Nat := 45

/-- Maximum total error mass (`falseReject + falseAccept`) for balanced effective use. -/
def maxGateErrorMassBalanced : Nat := 35

/-- Nominal legit demand on the 0–100 calibration dial (full channel). -/
def nominalLegitDemand : Nat := 100

/-! ## Throughput vs error (Pareto-style dial; same shape as protocol deficit) -/

/-- Combined false reject + false accept on the 0–100 normalized dial. -/
def gateErrorMass (m : GateMetrics) : Nat :=
  m.falseReject + m.falseAccept

/-- Unserved legit demand vs nominal channel (100): same as `protocolDeficit` when
    `paths = nominalLegitDemand` and `streams = m.legitThroughput`. -/
def gateProtocolDeficit (m : GateMetrics) : Nat :=
  nominalLegitDemand - m.legitThroughput

theorem gate_protocol_deficit_is_protocol_deficit (m : GateMetrics) :
    gateProtocolDeficit m =
      protocolDeficit nominalLegitDemand m.legitThroughput := by
  rfl

/-! ## Skyrms–stag toy: coordination fraction ↔ metrics (calibration story) -/

/-- `stagAdoption` ∈ [0,100]: population weight on the payoff-dominant stag convention.
    Low values model risk-dominant hare lock; high values model coordinated stag. -/
structure StagHuntConvention where
  stagAdoption : Nat
  deriving Repr

/-- Unrealized mutual-stag capacity on the same dial as `gateProtocolDeficit`. -/
def conventionDeficit (c : StagHuntConvention) : Nat :=
  nominalLegitDemand - c.stagAdoption

/-- Stylized identification: legit flow tracks stag adoption; “rejections” are
    hare-lock friction on the complementary mass. -/
def metricsFromStagConvention (c : StagHuntConvention) : GateMetrics where
  falseReject := nominalLegitDemand - c.stagAdoption
  falseAccept := 0
  legitThroughput := c.stagAdoption

theorem metrics_from_stag_throughput (c : StagHuntConvention) :
    (metricsFromStagConvention c).legitThroughput = c.stagAdoption := by
  rfl

theorem deficit_agrees_for_stag_metrics (c : StagHuntConvention) :
    gateProtocolDeficit (metricsFromStagConvention c) = conventionDeficit c := by
  rfl

theorem error_mass_agrees_with_deficit_stag_toy (c : StagHuntConvention) :
    gateErrorMass (metricsFromStagConvention c) = gateProtocolDeficit (metricsFromStagConvention c) := by
  simp [gateErrorMass, gateProtocolDeficit, metricsFromStagConvention, Nat.add_zero]

/-- Risk-dominant hare lock: stag adoption stays at or below 40 on the toy dial. -/
def IsRiskDominantHareLock (c : StagHuntConvention) : Prop :=
  c.stagAdoption ≤ 40

theorem hare_lock_implies_high_protocol_deficit (c : StagHuntConvention)
    (hlock : IsRiskDominantHareLock c) :
    gateProtocolDeficit (metricsFromStagConvention c) ≥ nominalLegitDemand - 40 := by
  unfold gateProtocolDeficit metricsFromStagConvention IsRiskDominantHareLock nominalLegitDemand at *
  /- `Nat.sub_le_sub_left` (Init): `n ≤ m → k - m ≤ k - n` with `n = stag`, `m = 40`, `k = 100`. -/
  exact Nat.sub_le_sub_left hlock nominalLegitDemand

/-! ## Effective vs ineffective (usage classification) -/

/-- Effective gatekeeping:
    * If a serious bottleneck is on record, false accepts stay bounded.
    * False rejects stay below the effective ceiling.
    * If appeals exist, false rejects stay tighter (procedural load is honored). -/
def IsEffective (g : Gate) (m : GateMetrics) : Prop :=
  (g.bottleneck < hazardThreshold ∨ m.falseAccept ≤ maxFalseAcceptUnderHazard) ∧
  m.falseReject ≤ maxFalseRejectEffective ∧
  (g.appealPath → m.falseReject ≤ maxFalseRejectWithAppeal)

/-- Ineffective or harmful usage patterns (any disjunct suffices):
    * Rent-shaped: no bottleneck but high strictness and high false rejects.
    * Failed protection: bottleneck is serious but false accepts blow the budget.
    * HiddenCriteria without recourse: high opacity, no appeal, elevated false rejects. -/
def IsIneffectiveUsage (g : Gate) (m : GateMetrics) : Prop :=
  (g.bottleneck = 0 ∧ g.strictness ≥ rentStrictnessFloor ∧ m.falseReject ≥ falseRejectPain) ∨
  (g.bottleneck ≥ hazardThreshold ∧ m.falseAccept > failedContainmentFalseAccept) ∨
  (g.opacity ≥ highOpacity ∧ g.appealPath = false ∧ m.falseReject ≥ falseRejectPain - 5)

/-- Balanced effective: effective gate + throughput floor + error budget
    (joint witness — stronger than `IsEffective` alone). -/
def IsEffectiveBalanced (g : Gate) (m : GateMetrics) : Prop :=
  IsEffective g m ∧
  m.legitThroughput ≥ minLegitThroughputEffective ∧
  gateErrorMass m ≤ maxGateErrorMassBalanced

theorem balanced_effective_implies_effective (g : Gate) (m : GateMetrics)
    (h : IsEffectiveBalanced g m) : IsEffective g m :=
  h.1

theorem balanced_high_throughput (g : Gate) (m : GateMetrics) (h : IsEffectiveBalanced g m) :
    m.legitThroughput ≥ minLegitThroughputEffective :=
  h.2.1

/-! ## Structural lemmas (spec-level unpacking) -/

theorem effective_implies_false_reject_cap (g : Gate) (m : GateMetrics) (h : IsEffective g m) :
    m.falseReject ≤ maxFalseRejectEffective := by
  rcases h with ⟨_, hfr, _⟩
  exact hfr

theorem effective_with_appeal_tighter_cap (g : Gate) (m : GateMetrics)
    (h : IsEffective g m) (ha : g.appealPath = true) :
    m.falseReject ≤ maxFalseRejectWithAppeal := by
  rcases h with ⟨_, _, happeal⟩
  exact happeal ha

theorem effective_hazard_bounds_false_accept (g : Gate) (m : GateMetrics)
    (h : IsEffective g m) (hb : g.bottleneck ≥ hazardThreshold) :
    m.falseAccept ≤ maxFalseAcceptUnderHazard := by
  rcases h with ⟨hor, _, _⟩
  cases hor with
  | inl hlt =>
    exfalso
    exact Nat.not_lt_of_le hb hlt
  | inr hfa =>
    exact hfa

theorem failed_protection_unpack (g : Gate) (m : GateMetrics)
    (hfail : g.bottleneck ≥ hazardThreshold ∧ m.falseAccept > failedContainmentFalseAccept) :
    m.falseAccept > failedContainmentFalseAccept ∧ g.bottleneck ≥ hazardThreshold :=
  ⟨hfail.2, hfail.1⟩

/-- Rent-shaped ineffective pattern: zero bottleneck, strict gate, painful false rejects. -/
def IsRentShaped (g : Gate) (m : GateMetrics) : Prop :=
  g.bottleneck = 0 ∧ g.strictness ≥ rentStrictnessFloor ∧ m.falseReject ≥ falseRejectPain

theorem rent_shaped_implies_ineffective (g : Gate) (m : GateMetrics) (h : IsRentShaped g m) :
    IsIneffectiveUsage g m := by
  left
  exact h

/-- Effective usage contradicts rent-shaped ineffective at the stated numeric thresholds. -/
theorem effective_and_rent_shaped_contradiction (g : Gate) (m : GateMetrics)
    (heff : IsEffective g m) (hrent : IsRentShaped g m) : False := by
  rcases hrent with ⟨_, _, hfr⟩
  rcases heff with ⟨_, hcap, _⟩
  have h6055 : 60 ≤ 55 := Nat.le_trans hfr hcap
  exact absurd h6055 (by decide)

/-! ## Where + how hints (classification helpers, not social theorems) -/

/-- Risk or scarcity carriers often allow higher strictness before rent suspicion. -/
def carrier_often_constraint_tracking (c : GateCarrier) : Prop :=
  c = GateCarrier.risk ∨ c = GateCarrier.scarcity

/-- HiddenCriteria style without appeals is procedurally fragile regardless of carrier. -/
def hiddenCriteria_without_recourse (g : Gate) : Prop :=
  g.style = GateStyle.hiddenCriteria ∧ g.appealPath = false

theorem hiddenCriteria_without_recourse_implies_ineffective (g : Gate) (m : GateMetrics)
    (hop : g.opacity ≥ highOpacity) (_hstyle : g.style = GateStyle.hiddenCriteria)
    (hno : g.appealPath = false) (hfr : m.falseReject ≥ falseRejectPain - 5) :
    IsIneffectiveUsage g m := by
  right; right
  exact ⟨hop, hno, hfr⟩

/-! ## Worked witness (concrete configuration) -/

def example_hazard_gate : Gate where
  carrier := GateCarrier.risk
  episteme := { repeated := true, asymmetricInfo := true }
  style := GateStyle.publishedThreshold
  strictness := 70
  opacity := 10
  appealPath := true
  bottleneck := 80

def example_hazard_metrics : GateMetrics where
  falseReject := 25
  falseAccept := 8
  legitThroughput := 70

theorem example_hazard_gate_is_effective : IsEffective example_hazard_gate example_hazard_metrics := by
  constructor
  · right; decide
  · constructor
    · decide
    · intro; decide

theorem example_hazard_gate_is_balanced : IsEffectiveBalanced example_hazard_gate example_hazard_metrics := by
  refine ⟨example_hazard_gate_is_effective, ?_, ?_⟩
  · decide
  · decide

def example_rent_gate : Gate where
  carrier := GateCarrier.attention
  episteme := { repeated := true, asymmetricInfo := false }
  style := GateStyle.hiddenCriteria
  strictness := 75
  opacity := 90
  appealPath := false
  bottleneck := 0

def example_rent_metrics : GateMetrics where
  falseReject := 72
  falseAccept := 5
  legitThroughput := 20

theorem example_rent_is_ineffective : IsIneffectiveUsage example_rent_gate example_rent_metrics := by
  left
  exact ⟨rfl, by decide, by decide⟩

theorem example_rent_not_effective : ¬ IsEffective example_rent_gate example_rent_metrics := by
  intro he
  have hrent : IsRentShaped example_rent_gate example_rent_metrics := by
    refine ⟨rfl, ?_, ?_⟩
    · decide
    · decide
  exact effective_and_rent_shaped_contradiction _ _ he hrent

end Gatekeeping
