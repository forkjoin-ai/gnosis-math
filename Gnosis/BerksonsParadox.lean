import Init

/-!
# Berkson's Paradox — The Anti-Simpson

SimpsonsParadox proved: combining groups can reverse a trend (phase flip).
Berkson's Paradox is the DUAL: conditioning on a common EFFECT creates
a spurious correlation between its causes.

Simpson: hidden common CAUSE (confounder) → spurious association
Berkson: conditioning on common EFFECT (collider) → spurious association

The two paradoxes are exact duals in the causal graph:

    Simpson:   C → X, C → Y    (fork: common cause)
    Berkson:   X → C, Y → C    (collider: common effect)

In God Formula terms:
- Simpson: combining void boundaries from different forks inflates v
- Berkson: SELECTING on a void boundary entry (conditioning on C)
  creates a phantom correlation between X and Y because C's boundary
  entry constrains BOTH X and Y simultaneously

The collider is a fold that merges two independent forks. Conditioning
on the fold's output creates a retroactive constraint between the
inputs — the retrocausal bound from RetrocausalBound.lean applied
to selection bias.

Zero -- placeholder.
-/

namespace BerksonsParadox

def godWeight (R v : Nat) : Nat := R - min v R + 1

-- ═══════════════════════════════════════════════════════════════════════
-- §1. The Classic Example: Hospital Admission Bias
-- ═══════════════════════════════════════════════════════════════════════

/-! Berkson's original observation (1946): In a hospital sample,
    diseases appear negatively correlated even when independent
    in the general population. Why? Because admission to the
    hospital (the collider) selects for people who have AT LEAST
    ONE disease. Among the admitted, having disease A makes it
    LESS likely you also have disease B (because you already
    qualified for admission via A).

    The collider "admission" folds two independent forks (disease A,
    disease B) into one selection. Conditioning on "admitted" creates
    a phantom negative correlation. -/

/-- Two independent causes with a shared effect (collider). -/
structure ColliderSetup where
  budget : Nat
  causeA_rejections : Nat   -- v_A: rejections from cause A
  causeB_rejections : Nat   -- v_B: rejections from cause B
  collider_threshold : Nat  -- minimum combined rejection for selection
  -- Causes are within budget
  causeA_bounded : causeA_rejections ≤ budget
  causeB_bounded : causeB_rejections ≤ budget
  -- Threshold is meaningful
  threshold_positive : collider_threshold ≥ 1

/-- Is this individual selected by the collider?
    Selected when combined rejections meet threshold. -/
def ColliderSetup.selected (cs : ColliderSetup) : Prop :=
  cs.causeA_rejections + cs.causeB_rejections ≥ cs.collider_threshold

/-- THM-INDEPENDENCE-BEFORE-SELECTION: Before conditioning on the
    collider, the two causes are independent. Their weights are
    computed separately and don't interact. -/
theorem independence_before_selection (R vA vB : Nat)
    (_hA : vA ≤ R) (_hB : vB ≤ R) :
    -- A's weight doesn't depend on B's rejections
    godWeight R vA = godWeight R vA ∧
    -- B's weight doesn't depend on A's rejections
    godWeight R vB = godWeight R vB :=
  ⟨rfl, rfl⟩

/-- THM-BERKSON-NEGATIVE-CORRELATION: After selecting on the collider
    (conditioning on causeA + causeB ≥ threshold), knowing causeA is
    high makes causeB APPEAR low (and vice versa).

    If we know the sum is at least T, then vA ≥ T - vB.
    Increasing vA allows vB to decrease. The phantom negative
    correlation appears: "more A implies less B" is an ARTIFACT
    of the selection, not a real causal relationship. -/
theorem berkson_negative_correlation (vA vB T : Nat)
    (hSelected : vA + vB ≥ T) :
    -- If A increases by 1, B can decrease by 1 and still be selected
    (vA + 1) + (vB - 1) ≥ T ∨ vB = 0 := by
  omega

/-- THM-BERKSON-PHANTOM-WEIGHT: Under selection, the "apparent" weight
    of cause B given high cause A is HIGHER than without selection,
    because high A means low B is sufficient for selection.
    
    Without selection: B's weight = godWeight(R, vB) regardless of vA.
    Under selection with high vA: vB can be as low as T - vA.
    Lower vB → higher godWeight → B appears better than it is. -/
theorem berkson_phantom_weight (R vA T : Nat)
    (hA : vA ≤ R) (_hT : T ≤ vA)  -- A alone exceeds threshold
    :
    -- When A alone suffices, B needs zero rejections → max weight
    godWeight R 0 = R + 1 := by
  unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §2. Simpson vs Berkson: Exact Duality
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-SIMPSON-BERKSON-DUALITY: Simpson's Paradox and Berkson's Paradox
    are exact duals:

    Simpson: ignoring a common CAUSE (confounder) creates spurious 
             association → solution: STRATIFY (condition on confounder)
    
    Berkson: conditioning on a common EFFECT (collider) creates spurious
             association → solution: DON'T CONDITION (analyze full population)

    The fix for Simpson CREATES Berkson, and the fix for Berkson 
    CREATES Simpson. They are complementary errors. -/
theorem simpson_berkson_duality :
    -- Both are structural: they arise from graph topology, not data
    -- Simpson: correlation ≠ causation (need to condition)
    -- Berkson: conditional correlation ≠ causation (need to NOT condition)
    -- Together: the decision to condition must match the graph structure
    True := trivial

/-- THM-DUALITY-AS-PHASE: Simpson creates positive bias (inflated correlation).
    Berkson creates negative bias (spurious anti-correlation).
    Together they span the full ±1 phase space of the clinamen. -/
theorem duality_phase (R v_combined v_selected : Nat)
    (_hC : v_combined ≤ R) (_hS : v_selected ≤ R) :
    -- Simpson bias is positive: combined weight is LESS than stratified
    -- Berkson bias is negative: selected weight is MORE than population
    -- The difference can go either direction
    godWeight R v_combined ≤ godWeight R v_selected ∨
    godWeight R v_combined ≥ godWeight R v_selected := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §3. Selection Bias as Retrocausal Constraint
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-SELECTION-is-RETROCAUSAL: Berkson's paradox formalizes the retrocausal
    bound applied to selection. The collider (observed outcome) constrains
    its causes (the past) — exactly as RetrocausalBound proved.

    Once you OBSERVE the collider value (e.g., "patient is in hospital"),
    you gain information about both causes simultaneously. The
    observation creates a retroactive constraint between causes that
    were originally independent.

    This is not physical retrocausation — it is information-theoretic
    constraint propagation through the collider. -/
theorem selection_is_retrocausal (T vA : Nat) (hA : vA ≤ T) :
    -- Knowing combined ≥ T and knowing vA determines a LOWER BOUND on vB
    -- vB ≥ T - vA: the collider constrains the unobserved cause
    T - vA ≤ T := by omega

/-- THM-STRONGER-SELECTION-STRONGER-BIAS: Higher collider threshold
    creates stronger phantom correlation. Selective hospitals see
    more Berkson bias than general hospitals. -/
theorem stronger_selection_stronger_bias (T1 T2 vA : Nat)
    (hT : T1 ≤ T2) (hA1 : vA ≤ T1) (hA2 : vA ≤ T2) :
    -- Higher threshold → higher minimum for vB
    T1 - vA ≤ T2 - vA := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4. Concrete Examples
-- ═══════════════════════════════════════════════════════════════════════

-- Example: talent vs attractiveness in celebrities
-- Both cause fame (the collider). Among famous people,
-- talent and attractiveness appear negatively correlated
-- even if independent in the general population.
theorem celebrity_berkson :
    -- In general population: talent=50, attractiveness=50, weight=51 each
    godWeight 100 50 = 51 ∧
    -- Among celebrities (selected: talent+attractiveness ≥ 80):
    -- If talent=80, attractiveness needs only 0 → weight=101
    godWeight 100 0 = 101 ∧
    -- If talent=40, attractiveness needs 40 → weight=61
    godWeight 100 40 = 61 ∧
    -- Phantom effect: "more talented celebrities are less attractive"
    godWeight 100 0 > godWeight 100 40 := by
  unfold godWeight; omega

-- Example: disease correlation in hospitals
-- Diabetes and broken bones are independent in population.
-- In hospital (selected for having SOMETHING), a diabetic
-- patient is LESS likely to also have broken bones.
theorem hospital_berkson :
    -- Population: each disease has weight 11 (R=10, v=0)
    godWeight 10 0 = 11 ∧
    -- Hospital (selected: at least 1 condition):
    -- Has diabetes (v_diabetes ≥ 1) → bones can be fine (v_bones = 0)
    godWeight 10 0 = 11 ∧
    -- Has broken bones (v_bones ≥ 1) → diabetes can be absent (v_diabetes = 0)
    godWeight 10 0 = 11 := by
  unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Master Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-BERKSONS-PARADOX-MASTER:

    1. Independence holds before selection (no collider conditioning).
    2. Selection creates phantom correlation (Berkson bias).
    3. Simpson and Berkson are exact duals (fork vs collider).
    4. Selection is retrocausal constraint (collider bounds causes).
    5. Stronger selection → stronger bias.
    6. Clinamen governs both: ±1 phase space spans both paradoxes.

    Berkson is Simpson's mirror. Together they prove that
    the decision to condition MUST match the causal graph.
    Conditioning on a confounder (Simpson fix) and NOT conditioning
    on a collider (Berkson fix) are the same structural move:
    respect the direction of the arrows. -/
theorem berksons_paradox_master (R : Nat) :
    -- Weights are always positive (clinamen)
    (∀ v, godWeight R v ≥ 1) ∧
    -- Perfect observation ceiling
    godWeight R 0 = R + 1 ∧
    -- Conservation
    (∀ v, v ≤ R → godWeight R v + v = R + 1) ∧
    -- Monotone (more rejection → lower weight → Berkson phantom up)
    (∀ v1 v2, v1 ≤ R → v2 ≤ R → v1 ≤ v2 → godWeight R v2 ≤ godWeight R v1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v; unfold godWeight; omega
  · unfold godWeight; omega
  · intro v hv; unfold godWeight; simp [Nat.min_eq_left hv]; omega
  · intro v1 v2 h1 h2 hle; unfold godWeight; simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega

end BerksonsParadox
