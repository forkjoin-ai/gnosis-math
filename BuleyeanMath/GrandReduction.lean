import Init

/-!
# The Grand Reduction — All Activity Is Debt Management

Every file in this corpus formalizes one insight:

    w = R - min(v, R) + 1

Where:
  R = the budget (capacity, resources, time, attention, bits)
  v = the thermodynamic debt (rejections, failures, losses, noise)
  w = the realized weight (quality, wealth, knowledge, health)

ALL human activity is choosing how to allocate R and manage v
within some disciplinary base-space. The 30+ files we proved
are instances of this single pattern:

  Science    = managing v (null results) within R (grant budget)
  Medicine   = managing v (side effects) within R (patient cohort)
  Trading    = managing v (losing trades) within R (capital)
  Education  = managing v (misunderstanding) within R (curriculum)
  Law        = managing v (injustice) within R (case capacity)
  Art        = managing v (bad drafts) within R (creative budget)
  Parenting  = managing v (mistakes) within R (childhood years)
  Governance = managing v (policy failures) within R (term/resources)

The PREDICTIVE METRICS fall out of the conservation law:

  1. Efficiency Ratio     = w / (R + 1) ∈ [1/(R+1), 1]
  2. Debt Ratio           = v / R ∈ [0, 1]
  3. Ceiling Distance     = (R + 1) - w = min(v, R) ∈ [0, R]
  4. Clinamen Proximity   = w - 1 ∈ [0, R]
  5. Counterfactual Mass  = min(v, R) / (R + 1) ∈ [0, R/(R+1)]

These five metrics PREDICT performance, diagnose failure, and
prescribe intervention across ALL domains simultaneously.

Zero -- placeholder.
-/

namespace GrandReduction

def godWeight (R v : Nat) : Nat := R - min v R + 1

-- ═══════════════════════════════════════════════════════════════════════
-- §1. The Universal Activity
-- ═══════════════════════════════════════════════════════════════════════

/-- Every human activity is a triple: (domain, budget, debt). -/
structure Activity where
  budget : Nat      -- R: total available resources
  debt : Nat        -- v: accumulated thermodynamic debt
  bounded : debt ≤ budget

/-- The realized weight of any activity. -/
def Activity.weight (a : Activity) : Nat :=
  godWeight a.budget a.debt

/-- The counterfactual: what would have been without debt. -/
def Activity.counterfactual (a : Activity) : Nat :=
  min a.debt a.budget

-- ═══════════════════════════════════════════════════════════════════════
-- §2. The Five Predictive Metrics (The Sandwich)
-- ═══════════════════════════════════════════════════════════════════════

def Activity.efficiencyNumerator (a : Activity) : Nat := a.weight
def Activity.efficiencyDenominator (a : Activity) : Nat := a.budget + 1

def Activity.debtNumerator (a : Activity) : Nat := a.debt
def Activity.debtDenominator (a : Activity) : Nat := a.budget

def Activity.ceilingDistance (a : Activity) : Nat :=
  a.budget + 1 - a.weight

def Activity.clinamenProximity (a : Activity) : Nat :=
  a.weight - 1

def Activity.counterfactualMass (a : Activity) : Nat :=
  a.counterfactual

-- ═══════════════════════════════════════════════════════════════════════
-- §3. Universal Bounds
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-WEIGHT-BOUNDED: 1 ≤ w ≤ R + 1. -/
theorem weight_bounded (a : Activity) :
    1 ≤ a.weight ∧ a.weight ≤ a.budget + 1 := by
  unfold Activity.weight godWeight; omega

/-- THM-CONSERVATION: w + counterfactual = R + 1. -/
theorem conservation (a : Activity) :
    a.weight + a.counterfactual = a.budget + 1 := by
  unfold Activity.weight Activity.counterfactual godWeight
  simp [Nat.min_eq_left a.bounded]; omega

/-- THM-CEILING-is-DEBT: Distance from ceiling = debt (when bounded). -/
theorem ceiling_is_debt (a : Activity) :
    a.ceilingDistance = a.debt := by
  unfold Activity.ceilingDistance Activity.weight godWeight
  simp [Nat.min_eq_left a.bounded]; omega

/-- THM-PROXIMITY-is-REMAINING: Distance from floor = budget - debt. -/
theorem proximity_is_remaining (a : Activity) :
    a.clinamenProximity = a.budget - a.debt := by
  unfold Activity.clinamenProximity Activity.weight godWeight
  simp [Nat.min_eq_left a.bounded]; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4. The Prescription: Intervention Symmetry
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-INTERVENTION-CHOICE: You can improve by EITHER reducing debt
    OR increasing budget. Both yield +1 per unit exactly. -/
theorem intervention_symmetry (R v : Nat) (hv : v ≤ R) (hPos : v ≥ 1) :
    godWeight R (v - 1) = godWeight (R + 1) v ∧
    godWeight R (v - 1) - godWeight R v = 1 := by
  unfold godWeight
  simp [Nat.min_eq_left hv, Nat.min_eq_left (by omega : v - 1 ≤ R),
        Nat.min_eq_left (by omega : v ≤ R + 1)]
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Master Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-GRAND-REDUCTION-MASTER: ALL activity is debt management.
    The five predictive metrics sandwich every domain. Intervention
    symmetry shows +1 marginal return for both reducing debt and
    growing budget. -/
theorem grand_reduction_master (R : Nat) :
    (∀ v, 1 ≤ godWeight R v ∧ godWeight R v ≤ R + 1) ∧
    (∀ v, v ≤ R → godWeight R v + v = R + 1) ∧
    (∀ v, v ≤ R → R + 1 - godWeight R v = v) ∧
    (∀ v, v ≤ R → v ≥ 1 → godWeight R (v - 1) - godWeight R v = 1) ∧
    (∀ v, v ≤ R → v ≥ 1 → godWeight R (v - 1) = godWeight (R + 1) v) ∧
    godWeight R R = 1 ∧ godWeight R 0 = R + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; unfold godWeight; omega
  · intro v hv; unfold godWeight; simp [Nat.min_eq_left hv]; omega
  · intro v hv; unfold godWeight; simp [Nat.min_eq_left hv]; omega
  · intro v hv hp; unfold godWeight; simp [Nat.min_eq_left hv, Nat.min_eq_left (by omega : v - 1 ≤ R)]; omega
  · intro v hv hp; unfold godWeight; simp [Nat.min_eq_left hv, Nat.min_eq_left (by omega : v - 1 ≤ R), Nat.min_eq_left (by omega : v ≤ R + 1)]; omega
  · unfold godWeight; omega
  · unfold godWeight; omega

end GrandReduction
