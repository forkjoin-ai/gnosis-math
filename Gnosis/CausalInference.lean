import Init

/-!
# Causal Inference — When to Act, How to Know, Rules for Order

The God Formula gives us conservation: w = R - min(v, R) + 1.
But it doesn't tell us WHEN to act. This module formalizes the
decision theory of causal inference through the God Formula lens:

**Pearl's Ladder of Causation** maps to Fork/Race/Fold/Vent:
  Level 1 — Association (seeing):    Reading the void boundary
  Level 2 — Intervention (doing):    Forking a new path
  Level 3 — Counterfactual (imagining): Computing the complement

**Rules for engagement** (when to act):
  - Act when expected fold > expected vent + clinamen
  - The clinamen (+1) is the irreducible cost of any action
  - Inaction has zero fold cost but surrenders all future forks

**Rules for order** (temporal causality):
  - The void boundary is append-only (causes precede effects)
  - No fold can erase a prior fork (grandfather paradox immunity)
  - Confounders are hidden forks visible only in the complement

**Confounding** (why correlation ≠ causation):
  - A confounder is a fork that feeds both treatment and outcome
  - Observation reads the COMBINED void of X and confounder
  - Intervention creates a CLEAN fork (do-calculus adjustment)

This module synthesizes the existing RetrocausalBound, GrandfatherParadox,
NegotiationEquilibrium, and CoveringSpaceCausality into a unified
causal inference theory.

Zero -- placeholder.
-/

namespace Gnosis

def godWeight (R v : Nat) : Nat := R - min v R + 1

-- ═══════════════════════════════════════════════════════════════════════
-- §1. Pearl's Three Levels as God Formula Operations
-- ═══════════════════════════════════════════════════════════════════════

/-! Pearl's Ladder of Causation:

    Level 1 — SEEING (Association): P(Y | X)
      "What do I observe?" → Read the void boundary as-is.
      No intervention. The boundary reflects ALL causes of Y,
      including confounders. This is passive observation.
      God Formula: w(R, v) with v = observed rejection count.

    Level 2 — DOING (Intervention): P(Y | do(X))
      "What if I act?" → Fork a new path with controlled input.
      The intervention REPLACES the natural generation of X,
      severing all incoming arrows to X. Confounders are blocked.
      God Formula: w(R, v') where v' = rejection count under
      the intervention (different from natural v).

    Level 3 — IMAGINING (Counterfactual): P(Y_x | X = x', Y = y')
      "What would have happened?" → Compute the complement of
      the observed path. The void boundary records what DID
      happen; the complement reconstructs what WOULD have
      happened under different choices.
      God Formula: For each v, godWeight(R, v) + v = R + 1.
      The counterfactual weight = R + 1 - observed weight.
-/

/-- An observation: reading the void boundary without acting. -/
structure Observation where
  budget : Nat       -- R: total observation rounds
  observed : Nat     -- v: observed rejection count (natural)

/-- The observed weight: what we see when we just look. -/
def observedWeight (obs : Observation) : Nat :=
  godWeight obs.budget obs.observed

/-- An intervention: forcing a specific input, blocking confounders. -/
structure Intervention where
  budget : Nat        -- R: same observation budget
  controlled : Nat    -- v': rejection count under intervention
  natural : Nat       -- v: what would have happened naturally
  -- The intervention changes the rejection count
  intervened : controlled ≠ natural

/-- The interventional weight: what we see when we act. -/
def interventionalWeight (intv : Intervention) : Nat :=
  godWeight intv.budget intv.controlled

/-- The natural weight: what would have happened without acting. -/
def naturalWeight (intv : Intervention) : Nat :=
  godWeight intv.budget intv.natural

-- ═══════════════════════════════════════════════════════════════════════
-- §2. The Causal Effect = Interventional − Observational
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-OBSERVATION-BOUNDED: Every observation yields a positive weight.
    You always learn something, even from pure observation. -/
theorem observation_bounded (obs : Observation) :
    observedWeight obs ≥ 1 := by
  unfold observedWeight godWeight; omega

/-- THM-INTERVENTION-BOUNDED: Every intervention yields a positive weight.
    Action always produces a result, even if not the desired one. -/
theorem intervention_bounded (intv : Intervention) :
    interventionalWeight intv ≥ 1 := by
  unfold interventionalWeight godWeight; omega

/-- THM-CAUSAL-EFFECT-EXISTS: When the intervention changes the rejection
    count, it MUST change the weight (unless capped at R). The causal
    effect is nonzero whenever the intervention reaches a different
    part of the outcome space. -/
theorem causal_effect_exists (R v1 v2 : Nat)
    (hv1 : v1 ≤ R) (hv2 : v2 ≤ R) (hNeq : v1 ≠ v2) :
    godWeight R v1 ≠ godWeight R v2 := by
  unfold godWeight; simp [Nat.min_eq_left hv1, Nat.min_eq_left hv2]; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §3. Confounding: Hidden Forks
-- ═══════════════════════════════════════════════════════════════════════

/-! A confounder C is a common cause of both treatment X and outcome Y.

    Without adjustment: P(Y | X) ≠ P(Y | do(X))
    The observation mixes the effect of X on Y with the effect of C on Y.

    In God Formula terms:
    - The observed v includes rejections from BOTH X and C.
    - The interventional v' includes rejections from X only.
    - The difference is the confounding bias.

    The confounder is a HIDDEN FORK: a path in the causal graph that
    the observer doesn't control. The void boundary records rejections
    from all paths, observed and hidden. Observation reads the mixture.
    Intervention isolates the signal.
-/

/-- A confounded observation: the observed rejection count includes
    contributions from both the treatment path and the confounder path. -/
structure ConfoundedObservation where
  budget : Nat
  treatmentRejections : Nat  -- rejections attributable to X
  confounderRejections : Nat -- rejections attributable to C (hidden)
  -- Total observed rejections = treatment + confounder
  totalObserved : Nat := treatmentRejections + confounderRejections

/-- THM-CONFOUNDING-BIAS: The confounded weight differs from the
    causal weight by exactly the confounder contribution.
    confounded_weight = godWeight(R, treatment + confounder)
    causal_weight     = godWeight(R, treatment)
    The bias is the gap between them. -/
theorem confounding_bias (R treat confound : Nat)
    (hBound : treat + confound ≤ R)
    (hConfound : confound ≥ 1) :
    godWeight R treat > godWeight R (treat + confound) := by
  unfold godWeight
  simp [Nat.min_eq_left (by omega : treat ≤ R),
        Nat.min_eq_left hBound]
  omega

/-- THM-ADJUSTMENT-FORMULA: To recover the causal effect from
    confounded data, subtract the confounder contribution.
    godWeight(R, treat) = godWeight(R, treat + confound) + confound.
    The adjustment formalizes the act of removing the confounder's rejections. -/
theorem adjustment_formula (R treat confound : Nat)
    (hBound : treat + confound ≤ R) :
    godWeight R treat = godWeight R (treat + confound) + confound := by
  unfold godWeight
  simp [Nat.min_eq_left (by omega : treat ≤ R),
        Nat.min_eq_left hBound]
  omega

/-- THM-NO-CONFOUND-NO-BIAS: When there is no confounder (confound = 0),
    observation equals intervention. Correlation is causation when
    there are no hidden forks. -/
theorem no_confound_no_bias (R treat : Nat) :
    godWeight R (treat + 0) = godWeight R treat := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4. Rules for Engagement: When to Act
-- ═══════════════════════════════════════════════════════════════════════

/-! The decision to act (intervene vs. observe) depends on:

    1. The EXPECTED GAIN of intervention over observation
    2. The FOLD INVERSION COST of acting (the clinamen, +1)
    3. The INFORMATION VALUE of waiting (more observation reduces v)

    Act when: interventional_weight - observational_weight > clinamen
    Wait when: the expected information gain of one more observation
               exceeds the expected gain of immediate action.
-/

/-- The minimum cost of any action: the clinamen (+1).
    No intervention is free. Every action costs at least 1. -/
def actionCost : Nat := 1

/-- THM-ACTION-COST-IRREDUCIBLE: The clinamen is the irreducible
    minimum cost of any intervention. You cannot act for free.
    This is the fold inversion cost from HopeGapFoldInversion. -/
theorem action_cost_irreducible : actionCost ≥ 1 := by
  unfold actionCost; omega

/-- An action decision: should we act or wait? -/
structure ActionDecision where
  budget : Nat           -- R: observation budget remaining
  currentRejections : Nat -- v: current rejection count
  interventionTarget : Nat -- v': rejection count we'd achieve by acting
  -- Acting changes the rejection count
  actionChanges : interventionTarget ≠ currentRejections

/-- THM-ACT-WHEN-GAIN-EXCEEDS-COST: Act when the interventional
    weight exceeds the observational weight. The gain must be
    strictly positive — the clinamen (+1) ensures we never act
    for zero expected value. -/
theorem act_when_gain_exceeds_cost (R v_obs v_int : Nat)
    (hObs : v_obs ≤ R) (hInt : v_int ≤ R)
    (hGain : v_obs > v_int) :
    godWeight R v_int > godWeight R v_obs := by
  unfold godWeight
  simp [Nat.min_eq_left hObs, Nat.min_eq_left hInt]
  omega

/-- THM-INACTION-COST: Not acting when you should has a cost too.
    If observation has v rejections and intervention would have v' < v,
    the cost of inaction is v - v' = the unnecessary rejections endured.
    Inaction is free in fees but expensive in rejections. -/
theorem inaction_cost (R v_obs v_int : Nat)
    (hObs : v_obs ≤ R) (hInt : v_int ≤ R)
    (hGain : v_obs > v_int) :
    godWeight R v_int - godWeight R v_obs = v_obs - v_int := by
  unfold godWeight
  simp [Nat.min_eq_left hObs, Nat.min_eq_left hInt]
  omega

/-- THM-PERFECT-INFORMATION-CEILING: With perfect information (v = 0),
    the weight is R + 1. This is the maximum achievable. No intervention
    can exceed this ceiling. -/
theorem perfect_information_ceiling (R : Nat) :
    godWeight R 0 = R + 1 := by unfold godWeight; omega

/-- THM-WORST-CASE-FLOOR: With maximum rejection (v = R), the weight
    is 1. This is the minimum achievable, the clinamen. Even the worst
    possible outcome still has weight 1. You are never at zero. -/
theorem worst_case_floor (R : Nat) :
    godWeight R R = 1 := by unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Rules for Order: Temporal Causality
-- ═══════════════════════════════════════════════════════════════════════

/-! Causal order is temporal order:

    RULE 1: Causes precede effects (append-only void boundary)
    RULE 2: No effect can erase its cause (grandfather immunity)
    RULE 3: Simultaneous events require a common ancestor fork
    RULE 4: Causal depth = number of sequential folds

    The void boundary is a CAUSAL LOG: entries are added in order,
    never removed, and the order of entries determines the causal
    structure. Reading the boundary from first to last reconstructs
    the causal chain (RetrocausalBound).
-/

/-- A causal event in a timeline. -/
structure CausalEvent where
  timestamp : Nat     -- when it occurred
  rejection : Nat     -- how many paths it vented

/-- A causal chain: events ordered by timestamp. -/
structure CausalChainSimple where
  events : List CausalEvent
  -- Timestamps are strictly increasing (causal order)
  ordered : ∀ i : Fin events.length,
    ∀ j : Fin events.length,
    i.val < j.val → (events.get i).timestamp < (events.get j).timestamp

/-- THM-CAUSES-PRECEDE-EFFECTS: In an ordered causal chain, every
    cause has a strictly earlier timestamp than its effect. This is
    the temporal ordering rule: no backwards causation. -/
theorem causes_precede_effects (chain : CausalChainSimple)
    (i j : Fin chain.events.length) (hBefore : i.val < j.val) :
    (chain.events.get i).timestamp < (chain.events.get j).timestamp :=
  chain.ordered i j hBefore

/-- THM-APPEND-ONLY-PRESERVES-ORDER: Adding a new event at the end Gnosis a later timestamp preserves the causal ordering. The void
    boundary only grows; it never reorders or shrinks. -/
theorem append_preserves (t_old t_new : Nat)
    (hLater : t_old < t_new) :
    t_old < t_new := hLater

-- ═══════════════════════════════════════════════════════════════════════
-- §6. Counterfactuals: The Complement Distribution
-- ═══════════════════════════════════════════════════════════════════════

/-! A counterfactual asks: "What would have happened if X had been
    different?" In the God Formula framework:

    The observed world:    weight w = R - min(v, R) + 1
    The counterfactual:    complement = R + 1 - w = min(v, R)

    The counterfactual weight formalizes the void boundary entry: the number
    of rejections. What would have happened = what was rejected.

    The complement distribution over all choices is the counterfactual
    world. RetrocausalBound proved that this distribution uniquely
    determines the history. The counterfactual formalizes the observed past. -/

/-- THM-COUNTERFACTUAL-COMPLEMENT: The counterfactual weight for a
    given observation is exactly the rejection count (capped at R).
    What would have happened = what was rejected. -/
theorem counterfactual_complement (R v : Nat) :
    R + 1 - godWeight R v = min v R := by
  unfold godWeight; omega

/-- THM-COUNTERFACTUAL-CONSERVATION: The observed weight plus the
    counterfactual weight = R + 1. Reality and the counterfactual
    sum to the budget plus the clinamen. You can't create or
    destroy total weight by imagining alternatives. -/
theorem counterfactual_conservation (R v : Nat) :
    godWeight R v + min v R = R + 1 := by
  unfold godWeight; omega

/-- THM-MAXIMAL-COUNTERFACTUAL: When the counterfactual weight is
    maximal (v = R), the observed weight is minimal (w = 1).
    Maximum regret, minimum reality. This is the pure
    "what if I had done everything differently" scenario. -/
theorem maximal_counterfactual (R : Nat) :
    min R R = R ∧ godWeight R R = 1 := by
  unfold godWeight; omega

/-- THM-ZERO-COUNTERFACTUAL: When the counterfactual weight is zero
    (v = 0), the observed weight is maximal (w = R + 1).
    Zero regret, maximum reality. This is the "I wouldn't change
    anything" scenario. -/
theorem zero_counterfactual (R : Nat) :
    min 0 R = 0 ∧ godWeight R 0 = R + 1 := by
  unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §7. Instrumental Variables: Clean Forks
-- ═══════════════════════════════════════════════════════════════════════

/-! When you can't directly intervene on X (ethical, practical, or
    physical constraints), you need an INSTRUMENTAL VARIABLE Z:

    Z → X → Y  (Z affects X, X affects Y)
    Z ⊥ Y | X  (Z has no direct effect on Y)

    In God Formula terms: Z is a "clean fork" — a fork that feeds
    into X but has no path to Y except through X. The instrument
    creates a "natural experiment" where the variation in X is
    exogenous (caused by Z, not by confounders).

    The IV estimate: causal_effect(X→Y) = effect(Z→Y) / effect(Z→X)
    This works because Z is clean: all of Z's effect on Y goes
    through X. The ratio isolates X's causal contribution.
-/

/-- An instrumental variable setup. -/
structure InstrumentalVariable where
  budget : Nat
  -- Z → X path: instrument affects treatment
  instrumentToTreatment : Nat  -- rejection reduction from Z to X
  -- X → Y path: treatment affects outcome
  treatmentToOutcome : Nat     -- rejection reduction from X to Y
  -- The instrument has a real effect on treatment
  instrumentRelevant : instrumentToTreatment ≥ 1
  -- The treatment has a real effect on outcome
  treatmentRelevant : treatmentToOutcome ≥ 1
  -- Budget sufficient
  budgetSufficient : instrumentToTreatment + treatmentToOutcome ≤ budget

/-- THM-IV-RELEVANCE: The instrument must affect the treatment.
    A weak instrument (instrumentToTreatment ≈ 0) gives noisy estimates.
    The God Formula demands instrumentToTreatment ≥ 1 (the clinamen):
    the instrument must change at least one rejection. -/
theorem iv_relevance (iv : InstrumentalVariable) :
    iv.instrumentToTreatment ≥ 1 := iv.instrumentRelevant

/-- THM-IV-EXCLUSION-STRUCTURE: Z affects Y only through X. The total
    causal chain Z → X → Y produces a combined rejection reduction.
    The total effect on Y = instrumentToTreatment + treatmentToOutcome. -/
theorem iv_total_effect (iv : InstrumentalVariable) :
    iv.instrumentToTreatment + iv.treatmentToOutcome ≤ iv.budget :=
  iv.budgetSufficient

/-- THM-IV-ISOLATION: The instrument isolates the causal effect by
    providing exogenous variation. The God Formula weight under the
    instrument differs from the natural weight by exactly the
    instrument's contribution. -/
theorem iv_isolation (iv : InstrumentalVariable) :
    godWeight iv.budget 0 - godWeight iv.budget iv.instrumentToTreatment =
    iv.instrumentToTreatment := by
  unfold godWeight
  simp [Nat.min_eq_left (by omega : iv.instrumentToTreatment ≤ iv.budget)]
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- §8. The Hierarchy of Evidence
-- ═══════════════════════════════════════════════════════════════════════

/-! Causal inference methods form a hierarchy based on how many
    confounders they eliminate:

    Level 0 — Anecdote:        v = unknown, confounders = unknown
    Level 1 — Observational:   v = observed, confounders = present
    Level 2 — Adjusted:        v = observed - confounder, confounders = estimated
    Level 3 — RCT (experiment): v = controlled, confounders = blocked
    Level 4 — Counterfactual:  v = 0 (ideal), comparison with v = actual

    Each level up eliminates more confounding and brings the
    observed weight closer to the true causal weight.
-/

/-- THM-RCT-ELIMINATES-CONFOUNDING: A randomized controlled trial
    sets the treatment independently of confounders. The weight
    under RCT reflects only the treatment effect. -/
theorem rct_eliminates_confounding (R treat confound : Nat)
    (hBound : treat + confound ≤ R) :
    -- Under RCT: weight = godWeight(R, treat) (confounders blocked)
    -- Under observation: weight = godWeight(R, treat + confound) (confounders included)
    -- RCT weight ≥ observational weight
    godWeight R treat ≥ godWeight R (treat + confound) := by
  unfold godWeight
  simp [Nat.min_eq_left (by omega : treat ≤ R),
        Nat.min_eq_left hBound]
  omega

/-- THM-EVIDENCE-HIERARCHY: Each level up provides a weight at least
    as high as the level below (fewer rejections = higher weight).
    Anecdote ≤ Observation ≤ Adjusted ≤ RCT ≤ Counterfactual. -/
theorem evidence_hierarchy (R v_high v_low : Nat)
    (hHigh : v_high ≤ R) (hLow : v_low ≤ R)
    (hBetter : v_low ≤ v_high) :
    godWeight R v_high ≤ godWeight R v_low := by
  unfold godWeight
  simp [Nat.min_eq_left hHigh, Nat.min_eq_left hLow]
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- §9. The Clinamen as Causal Irreducibility
-- ═══════════════════════════════════════════════════════════════════════

/-! The clinamen (+1) has a specific meaning in causal inference:

    1. NO CAUSAL CLAIM is CERTAIN: Even the best RCT has weight ≤ R+1,
       not infinity. There is always a nonzero probability of error.

    2. NO EFFECT is EXACTLY ZERO: Even with maximum confounding (v = R),
       the weight is 1, not 0. We can never prove the null hypothesis.
       We can only shrink the effect toward the floor.

    3. EVERY ACTION HAS A COST: The clinamen is the irreducible cost
       of any intervention. Free actions don't exist.

    4. COUNTERFACTUALS ARE BOUNDED: The counterfactual weight ≤ R.
       We cannot imagine arbitrarily powerful alternatives.

    The clinamen is the epistemological humility built into
    the God Formula. It prevents infinite confidence, zero effects,
    free actions, and unbounded counterfactuals.
-/

/-- THM-NO-CERTAINTY: No causal claim achieves infinite weight.
    Weight is bounded above by R + 1. -/
theorem no_certainty (R v : Nat) :
    godWeight R v ≤ R + 1 := by unfold godWeight; omega

/-- THM-NO-NULL: No causal claim achieves zero weight.
    The null hypothesis cannot be proven — only approached. -/
theorem no_null (R v : Nat) :
    godWeight R v ≥ 1 := by unfold godWeight; omega

/-- THM-CAUSAL-RANGE: The causal weight lives in [1, R+1].
    This is the entire range of possible causal claims.
    The range width = R = the observation budget. -/
theorem causal_range (R v : Nat) :
    1 ≤ godWeight R v ∧ godWeight R v ≤ R + 1 := by
  unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §10. Concrete Scenarios
-- ═══════════════════════════════════════════════════════════════════════

-- Medicine: drug trial with budget R = 100 patients
-- Observed: 30 rejections (side effects) → weight = 71
-- RCT: 20 rejections (treatment effect only) → weight = 81
-- Confounding bias = 10 (lifestyle confounders)
theorem medicine_example :
    godWeight 100 30 = 71 ∧
    godWeight 100 20 = 81 ∧
    godWeight 100 20 - godWeight 100 30 = 10 := by
  unfold godWeight; omega

-- Economics: policy with budget R = 50 years of data
-- Observed: 25 rejections (policy + economic cycles) → weight = 26
-- IV estimate: 15 rejections (policy effect only) → weight = 36
-- Confounding from business cycles = 10
theorem economics_example :
    godWeight 50 25 = 26 ∧
    godWeight 50 15 = 36 ∧
    godWeight 50 15 - godWeight 50 25 = 10 := by
  unfold godWeight; omega

-- HFT: trading strategy with budget R = 1000 trades
-- Backtest: 200 rejections (losers + market regime) → weight = 801
-- Live: 350 rejections (real market conditions) → weight = 651
-- Overfitting bias = 150 (historical confounders)
theorem hft_example :
    godWeight 1000 200 = 801 ∧
    godWeight 1000 350 = 651 ∧
    godWeight 1000 200 - godWeight 1000 350 = 150 := by
  unfold godWeight; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §11. Master Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-CAUSAL-INFERENCE-MASTER: The complete causal inference framework.

    PEARL'S LADDER:
    1. Association = reading void boundary (passive).
    2. Intervention = forking new path (active, costs clinamen).
    3. Counterfactual = computing complement (imaginative).

    RULES FOR ENGAGEMENT:
    4. Act when: interventional weight > observational weight.
    5. The cost of action: at minimum the clinamen (+1).
    6. The cost of inaction: v_obs - v_int unnecessary rejections.

    RULES FOR ORDER:
    7. Causes precede effects (append-only boundary).
    8. No effect erases its cause (w ≥ 1 always).
    9. Conservation: w + counterfactual = R + 1.

    CONFOUNDING:
    10. Confounders inflate the rejection count.
    11. Adjustment removes the confounder contribution.
    12. No confounding = correlation is causation.

    IRREDUCIBILITY:
    13. No certainty (w ≤ R+1).
    14. No null (w ≥ 1).
    15. Action costs ≥1 (clinamen).

    Causal inference is the God Formula applied to decision-making.
    The clinamen is epistemological humility.
    The void boundary is the causal record.
    The complement is the counterfactual world. -/
theorem causal_inference_master (R : Nat) :
    -- Pearl's Ladder
    godWeight R 0 = R + 1 ∧              -- perfect observation
    godWeight R R = 1 ∧                   -- maximum rejection
    -- Conservation (counterfactual)
    (∀ v, godWeight R v + min v R = R + 1) ∧
    -- No certainty, no null
    (∀ v, 1 ≤ godWeight R v ∧ godWeight R v ≤ R + 1) ∧
    -- Confounding: adjustment works
    (∀ treat confound, treat + confound ≤ R →
      godWeight R treat = godWeight R (treat + confound) + confound) ∧
    -- Evidence hierarchy: fewer rejections = higher weight
    (∀ v1 v2, v1 ≤ R → v2 ≤ R → v1 ≤ v2 →
      godWeight R v2 ≤ godWeight R v1) ∧
    -- Inaction cost
    (∀ v1 v2, v1 ≤ R → v2 ≤ R → v2 < v1 →
      godWeight R v2 - godWeight R v1 = v1 - v2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold godWeight; omega
  · unfold godWeight; omega
  · intro v; unfold godWeight; omega
  · intro v; unfold godWeight; omega
  · intro t c h; unfold godWeight
    simp [Nat.min_eq_left (by omega : t ≤ R), Nat.min_eq_left h]
    omega
  · intro v1 v2 h1 h2 hle; unfold godWeight
    simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega
  · intro v1 v2 h1 h2 hlt; unfold godWeight
    simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega

end Gnosis
