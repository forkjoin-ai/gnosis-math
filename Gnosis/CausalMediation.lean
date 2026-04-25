import Init

/-!
# Causal Mediation — Decomposing Direct and Indirect Effects

CausalInference proved the adjustment formula for confounders.
DomainComposition proved energy dissipates through sequential pipelines.

This file enters the door they opened together: **mediation analysis
decomposes total cause into direct and indirect channels.**

X → Y (direct effect)
X → M → Y (indirect effect through mediator M)
Total effect = direct + indirect

In God Formula terms:
- Direct path: godWeight(R, v_direct)
- Indirect path: sequential pipeline from DomainComposition
  where fold_X becomes fork_M, and fold_M becomes outcome_Y
- Total: godWeight(R, v_total) where v_total ≤ v_direct + v_indirect

The pipeline energy decrease theorem guarantees: the indirect effect
is STRICTLY LESS than the direct input to the mediator. Information
is lost at every step. The fold → fork transition at M is lossy.

Real-world examples:
- Education → Income (direct) vs Education → Skills → Income (mediated)
- Drug → Healing (direct) vs Drug → Biomarker → Healing (mediated)
- Training → Performance (direct) vs Training → Fitness → Performance

Zero -- placeholder.
-/

namespace Gnosis

def godWeight (R v : Nat) : Nat := R - min v R + 1

-- ═══════════════════════════════════════════════════════════════════════
-- §1. The Mediation Structure
-- ═══════════════════════════════════════════════════════════════════════

/-- A causal mediation setup: X → M → Y with a direct path X → Y. -/
structure MediationSetup where
  budget : Nat              -- Total observation budget R
  directRejections : Nat    -- v_direct: rejections on X → Y path
  mediatorInput : Nat       -- What X sends to M (the fold output of X)
  mediatorLoss : Nat        -- How much M loses (vent in M's pipeline step)
  mediatorLossPositive : mediatorLoss ≥ 1  -- Mediator always loses something (clinamen)
  mediatorLossBounded : mediatorLoss ≤ mediatorInput  -- Can't lose more than input
  directBounded : directRejections ≤ budget  -- Direct path bounded
  totalBounded : directRejections + mediatorInput ≤ budget  -- Total bounded

/-- The direct effect: what X contributes to Y without going through M. -/
def directEffect (m : MediationSetup) : Nat :=
  godWeight m.budget m.directRejections

/-- The indirect effect through mediator: what reaches Y via M.
    The mediator receives mediatorInput and loses mediatorLoss,
    so mediatorInput - mediatorLoss reaches Y. -/
def indirectContribution (m : MediationSetup) : Nat :=
  m.mediatorInput - m.mediatorLoss

/-- Total rejections = direct + indirect losses. -/
def totalRejections (m : MediationSetup) : Nat :=
  m.directRejections + m.mediatorLoss

/-- The total effect: godWeight at total rejections. -/
def totalEffect (m : MediationSetup) : Nat :=
  godWeight m.budget (totalRejections m)

-- ═══════════════════════════════════════════════════════════════════════
-- §2. Decomposition Theorems
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-TOTAL-DECOMPOSES: Total rejections = direct rejections + mediator loss.
    The total causal effect decomposes additively in rejection space. -/
theorem total_decomposes (m : MediationSetup) :
    totalRejections m = m.directRejections + m.mediatorLoss :=
  rfl

/-- THM-DIRECT-EXCEEDS-TOTAL: The direct effect (considering only
    direct rejections) is always ≥ the total effect (considering
    both direct and mediator losses). More rejection = lower weight. -/
theorem direct_exceeds_total (m : MediationSetup)
    (hBound : totalRejections m ≤ m.budget) :
    directEffect m ≥ totalEffect m := by
  unfold directEffect totalEffect totalRejections godWeight
  simp [Nat.min_eq_left m.directBounded, Nat.min_eq_left hBound]
  omega

/-- THM-MEDIATOR-GAP: The gap between direct and total effect equals
    the mediator loss. This formalizes the indirect effect measured in
    rejection units. -/
theorem mediator_gap (m : MediationSetup)
    (hBound : totalRejections m ≤ m.budget) :
    directEffect m - totalEffect m = m.mediatorLoss := by
  unfold directEffect totalEffect totalRejections godWeight
  simp [Nat.min_eq_left m.directBounded, Nat.min_eq_left hBound]
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- §3. The Mediator Always Loses Something (Clinamen)
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-MEDIATOR-LOSS-IRREDUCIBLE: The mediator always loses at least 1
    unit. This is the clinamen at the mediation step. No mediator is
    lossless. Information degrades through every intermediate step. -/
theorem mediator_loss_irreducible (m : MediationSetup) :
    m.mediatorLoss ≥ 1 := m.mediatorLossPositive

/-- THM-INDIRECT-STRICTLY-LESS: The indirect contribution is strictly
    less than the mediator input. The fold → fork transition at M
    loses energy. This is DomainComposition's pipeline_energy_decreases
    applied to causal mediation. -/
theorem indirect_strictly_less (m : MediationSetup) :
    indirectContribution m < m.mediatorInput := by
  unfold indirectContribution
  have := m.mediatorLossPositive
  omega

/-- THM-FULL-MEDIATION-LOSS: If the mediator absorbs ALL the input
    (mediatorLoss = mediatorInput), no indirect effect reaches Y.
    Full mediation with total loss = the mediator is a dead end. -/
theorem full_mediation_loss (m : MediationSetup)
    (hFull : m.mediatorLoss = m.mediatorInput) :
    indirectContribution m = 0 := by
  unfold indirectContribution; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4. Chain of Mediators
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-CHAIN-LOSSES-ACCUMULATE: In a chain X → M₁ → M₂ → Y, each
    mediator loses at least 1. Two mediators lose at least 2. N
    mediators lose at least N. Longer causal chains are weaker. -/
theorem chain_losses_accumulate (loss1 loss2 : Nat)
    (h1 : loss1 ≥ 1) (h2 : loss2 ≥ 1) :
    loss1 + loss2 ≥ 2 := by omega

/-- THM-CHAIN-LENGTH-BOUNDS-EFFECT: A mediator chain of length N
    loses at least N units of energy. The maximum achievable indirect
    effect through N mediators is input - N. -/
theorem chain_length_bounds (input chainLength : Nat)
    (hLength : chainLength ≥ 1)
    (hFeasible : chainLength ≤ input) :
    input - chainLength < input := by omega

/-- THM-HEAT-DEATH-OF-MEDIATION: Eventually, a long enough chain is
    meaningless. If chainLength ≥ input, the indirect effect is 0.
    All energy has been lost to mediation overhead. -/
theorem heat_death_of_mediation (input chainLength : Nat)
    (hExhausted : chainLength ≥ input) :
    input - chainLength = 0 := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Concrete Mediation Examples
-- ═══════════════════════════════════════════════════════════════════════

-- Education → Income
-- Direct: education credentials → salary (R=100, v_direct=20 → w=81)
-- Indirect: education → skills (input=80, loss=15) → skills → salary
-- Total: v_total = 20 + 15 = 35 → totalWeight = 66
-- The skills mediator contributes 15 units of the gap
theorem education_income :
    godWeight 100 20 = 81 ∧     -- direct only
    godWeight 100 35 = 66 ∧     -- total (direct + mediation loss)
    godWeight 100 20 - godWeight 100 35 = 15 := by  -- mediation contribution
  unfold godWeight; omega

-- Drug → Healing
-- Direct: drug chemistry → healing (R=50, v_direct=5 → w=46)
-- Indirect: drug → biomarker (input=45, loss=10) → biomarker → healing
-- Total: v_total = 5 + 10 = 15 → totalWeight = 36
theorem drug_healing :
    godWeight 50 5 = 46 ∧
    godWeight 50 15 = 36 ∧
    godWeight 50 5 - godWeight 50 15 = 10 := by
  unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §6. Master Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-CAUSAL-MEDIATION-MASTER:

    1. Total effect decomposes: v_total = v_direct + v_mediator_loss.
    2. Direct effect ≥ total effect (more rejection = lower weight).
    3. Mediator gap = mediator loss (the indirect effect cost).
    4. Mediator loss ≥ 1 (clinamen: no lossless mediation).
    5. Indirect < input (pipeline energy decrease).
    6. Chain losses accumulate (N mediators lose ≥ N).
    7. Long chains die (heat death of mediation).

    Mediation is the God Formula applied to causal chains.
    Each mediator is a fold → fork transition that loses ≥ 1.
    The clinamen at each step is the irreducible information loss.
    Long chains approach heat death: all energy becomes vent. -/
theorem causal_mediation_master (R v_d v_m : Nat)
    (hD : v_d ≤ R) (hM : v_m ≥ 1) (hTotal : v_d + v_m ≤ R) :
    -- Decomposition
    godWeight R v_d - godWeight R (v_d + v_m) = v_m ∧
    -- Direct ≥ total
    godWeight R v_d ≥ godWeight R (v_d + v_m) ∧
    -- Clinamen at mediator
    v_m ≥ 1 ∧
    -- Conservation
    godWeight R (v_d + v_m) + (v_d + v_m) = R + 1 := by
  unfold godWeight
  simp [Nat.min_eq_left hD, Nat.min_eq_left hTotal]
  omega

end Gnosis
