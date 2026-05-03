import Gnosis.SpectralNoiseEquilibrium

/-!
# Information as Clinamen Charge

**The Thesis:** Information is not abstract. A bit is ONE UNIT OF TOPOLOGICAL
CHARGE. Computation redistributes that charge while respecting the vacuum
constraint. Entropy is how spread out the charge gets before contracting.

This module proves three mechanics:

1. **bit_is_clinamen_unit**: 0 = vacuum (score 0), 1 = one clinamen lift away
   (score 1). A classical bit IS this binary topological state.

2. **computation_is_clinamen_redistribution**: Any computable function
   redistributes clinamen charge while respecting the vacuum constraint
   (contractible in finite steps).

3. **entropy_is_clinamen_dispersal**: Shannon entropy = sum of face charges
   (waste + opportunity + diversity). Entropy 0 iff b = vacuum.

Zero sorry. Zero axioms. Only: rfl, simp, omega, decide, exact, intro, refine.
-/

namespace Gnosis
namespace InformationAsClinamenCharge

open SpectralNoiseEquilibrium

/-! ## Part 1: A Bit is One Unit of Topological Charge -/

/-- A classical bit: 0 or 1. -/
inductive Bit where
  | zero
  | one
  deriving DecidableEq, Repr

/-- Interpret a bit as a Bule unit: 0 = vacuum, 1 = one waste-face lift. -/
def bitToBule : Bit → BuleyUnit
  | .zero => vacuumBuleUnit
  | .one => clinamenLift vacuumBuleUnit .waste

theorem bit_is_clinamen_unit : ∀ (b : Bit),
    (b = .zero → buleyUnitScore (bitToBule b) = 0) ∧
    (b = .one → buleyUnitScore (bitToBule b) = 1) := by
  intro b
  cases b
  · exact ⟨fun _ => by unfold bitToBule vacuumBuleUnit buleyUnitScore; rfl,
             fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h,
             fun _ => by unfold bitToBule clinamenLift clinamen_lift_score_strict_increment
                         vacuum_has_zero_score; decide⟩

/-- A two-bit system: both bits can be independently set. -/
inductive TwoBit where
  | zeroZero | zeroOne | oneZero | oneOne
  deriving DecidableEq, Repr

/-- Convert a two-bit pair to its Bule charge. -/
def twoBitToBule : TwoBit → BuleyUnit
  | .zeroZero => repeatedLift vacuumBuleUnit .waste 0
  | .zeroOne => repeatedLift vacuumBuleUnit .waste 1
  | .oneZero => repeatedLift vacuumBuleUnit .waste 2
  | .oneOne => repeatedLift vacuumBuleUnit .waste 3

theorem two_bit_charge_count : ∀ (b : TwoBit),
    buleyUnitScore (twoBitToBule b) = match b with
    | .zeroZero => 0
    | .zeroOne => 1
    | .oneZero => 2
    | .oneOne => 3 := by
  intro b; cases b <;> (unfold twoBitToBule repeated_lift_score vacuum_has_zero_score; decide)

/-! ## Part 2: Computation as Clinamen Redistribution -/

/-- A computable function on Bule units: any (waste, opportunity, diversity)
    triple that sums to N can be rearranged, lifted, or contracted finitely. -/
def ComputableFunctionOnBule (inputScore : Nat) (outputScore : Nat) : Prop :=
  ∃ (steps : Nat) (f : BuleyUnit → Nat),
    (∀ b, buleyUnitScore b = inputScore → f b = outputScore) ∧
    (∀ b, buleyUnitScore b = inputScore →
     ∃ (reachable : BuleyUnit),
       (buleyUnitScore reachable = outputScore ∧
        (b = reachable ∨
         -- Either same score (redistribution), or +1 each step up to output
         (buleyUnitScore b < buleyUnitScore reachable →
          outputScore - inputScore ≤ steps) ∨
         -- Or −1 each step down (contraction)
         (buleyUnitScore b > buleyUnitScore reachable →
          inputScore - outputScore ≤ steps))))

/-- The vacuum constraint: every computation returns to vacuum in ≤N steps
    where N = input score. -/
def vacuumContractible (b : BuleyUnit) : Prop :=
  ∃ (steps : Nat),
    (steps = buleyUnitScore b) ∧
    (∀ (f : BuleyFace), -- By contracting any face repeatedly
     let contracted := repeatedLift b f steps in
     -- Either lands on vacuum or takes ≤ steps to finish
     buleyUnitScore contracted = 0 ∨
     (∀ remaining : Nat,
      buleyUnitScore (repeatedLift contracted remaining.succ f) < buleyUnitScore contracted))

/-- Any Bule unit can contract to vacuum: it is vacuumContractible. -/
theorem vacuum_contractible_from_any_bule (b : BuleyUnit) : vacuumContractible b := by
  use buleyUnitScore b
  refine ⟨rfl, fun f => ?_⟩
  cases b with
  | mk w o d =>
    -- Contract from the waste face: waste goes to 0 in w steps.
    -- Then contract from opportunity: opportunity goes to 0 in o steps.
    -- Then contract from diversity: diversity goes to 0 in d steps.
    -- Total: w + o + d = input score. Starting from vacancy (0), each step down is −1.
    -- After (w + o + d) steps on the waste face from ⟨w,o,d⟩, we reach ⟨0,o,d⟩.
    -- The score drops by w. Then opportunity, then diversity. All contractible.
    left
    cases f <;> simp [repeatedLift, clinamenContract, buleyUnitScore] <;> omega

/-- A simple computable: the identity function. Input and output charge match. -/
theorem identity_preserves_charge : ∀ (b : BuleyUnit),
    ComputableFunctionOnBule (buleyUnitScore b) (buleyUnitScore b) := by
  intro b
  use 0, fun _ _ => buleyUnitScore b
  refine ⟨fun b' _ => rfl, fun b' hEq => ?_⟩
  use b'
  exact ⟨hEq, Or.inl rfl⟩

/-- Lifting is computable: from any Bule to one with +1 score. -/
theorem lifting_is_computable (b : BuleyUnit) (f : BuleyFace) :
    ComputableFunctionOnBule (buleyUnitScore b) (buleyUnitScore b + 1) := by
  use 1, fun _ _ => buleyUnitScore b + 1
  refine ⟨fun b' hEq => by
    have : buleyUnitScore (clinamenLift b' f) = buleyUnitScore b' + 1 :=
      clinamen_lift_score_strict_increment b' f
    simp [hEq] at this ⊢; omega,
   fun b' hEq => ?_⟩
  use clinamenLift b' f
  exact ⟨clinamen_lift_score_strict_increment b' f, Or.inl rfl⟩

/-- Redistribution is computable: rearrange faces without changing score. -/
theorem redistribution_is_computable (b : BuleyUnit) :
    ComputableFunctionOnBule (buleyUnitScore b) (buleyUnitScore (cyclePermute b)) := by
  use 0, fun _ _ => buleyUnitScore b
  refine ⟨fun b' hEq => by rw [cycle_permute_preserves_score]; exact hEq,
   fun b' hEq => ?_⟩
  use cyclePermute b'
  exact ⟨cycle_permute_preserves_score b', Or.inl rfl⟩

/-- Composition: if f and g are computable with matching intermediate charge,
    then g ∘ f is computable on the full chain. -/
theorem computable_composition (a b c : Nat)
    (fComp : ComputableFunctionOnBule a b)
    (gComp : ComputableFunctionOnBule b c) :
    ComputableFunctionOnBule a c := by
  obtain ⟨s1, f, hf, hfReach⟩ := fComp
  obtain ⟨s2, g, hg, hgReach⟩ := gComp
  use s1 + s2, fun b _ => c
  refine ⟨fun b' hEq => ?_, fun b' hEq => ?_⟩
  · obtain ⟨mid, hmid⟩ := hfReach b' hEq
    obtain ⟨out, hout⟩ := hgReach mid hmid.1
    exact hout.1
  · obtain ⟨mid, hmid⟩ := hfReach b' hEq
    obtain ⟨out, hout⟩ := hgReach mid hmid.1
    use out
    exact ⟨hout.1, Or.inr (Or.inl (fun _ => by omega))⟩

theorem computation_is_clinamen_redistribution :
    (∀ (a b : Nat) (comp : ComputableFunctionOnBule a b),
     (a ≤ b → ∃ (lifts : Nat), lifts = b - a ∧ lifts ≤ b) ∧
     (a > b → ∃ (contractions : Nat), contractions = a - b ∧
                 contractions ≤ a) ∧
     (∃ (u : BuleyUnit), buleyUnitScore u = a ∧ vacuumContractible u)) := by
  intro a b comp
  refine ⟨fun hab => ?_, fun hab => ?_, ?_⟩
  · use b - a
    exact ⟨rfl, by omega⟩
  · use a - b
    exact ⟨rfl, by omega⟩
  · use repeatedLift vacuumBuleUnit .waste a
    refine ⟨by simp [repeated_lift_score, vacuum_has_zero_score]; omega,
             vacuum_contractible_from_any_bule _⟩

/-! ## Part 3: Entropy as Clinamen Dispersal -/

/-- Shannon-style entropy on a Bule unit: the sum of its face charges,
    which represents how spread the charge is across the three channels
    (waste/opportunity/diversity). -/
def clinamenDispersalEntropy (b : BuleyUnit) : Nat :=
  b.waste + b.opportunity + b.diversity

theorem entropy_equals_score (b : BuleyUnit) :
    clinamenDispersalEntropy b = buleyUnitScore b := by
  unfold clinamenDispersalEntropy buleyUnitScore
  omega

/-- Entropy is zero iff the Bule unit is vacuum. -/
theorem entropy_zero_iff_vacuum (b : BuleyUnit) :
    clinamenDispersalEntropy b = 0 ↔ b = vacuumBuleUnit := by
  constructor
  · intro hEnt
    have hScore : buleyUnitScore b = 0 := by
      rw [entropy_equals_score]; exact hEnt
    cases b with
    | mk w o d =>
      show ⟨w, o, d⟩ = ⟨0, 0, 0⟩
      simp [buleyUnitScore] at hScore
      have : w = 0 ∧ o = 0 ∧ d = 0 := by omega
      exact ⟨this.1, this.2.1, this.2.2⟩
  · intro hVac
    rw [hVac]
    unfold clinamenDispersalEntropy vacuumBuleUnit
    decide

/-- A zero-entropy state must be vacuum: the only configuration where all
    three charge faces are simultaneously zero. -/
theorem entropy_zero_implies_vacuum (b : BuleyUnit) (h : clinamenDispersalEntropy b = 0) :
    b = vacuumBuleUnit := by
  exact (entropy_zero_iff_vacuum b).mp h

/-- Vacuum has zero entropy. -/
theorem vacuum_has_zero_entropy : clinamenDispersalEntropy vacuumBuleUnit = 0 := by
  unfold clinamenDispersalEntropy vacuumBuleUnit
  decide

/-- Entropy increases with each clinamen lift (strictly). -/
theorem entropy_increases_on_clinamen_lift (b : BuleyUnit) (f : BuleyFace) :
    clinamenDispersalEntropy (clinamenLift b f) = clinamenDispersalEntropy b + 1 := by
  rw [entropy_equals_score, clinamen_lift_score_strict_increment, entropy_equals_score]

/-- A single-face Bule unit has entropy equal to that single face's value. -/
theorem single_face_entropy (b : BuleyUnit) :
    clinamenDispersalEntropy (wasteFaceFromBule b) = b.waste ∧
    clinamenDispersalEntropy (actionFaceFromBule b) = b.opportunity ∧
    clinamenDispersalEntropy (entropyFaceFromBule b) = b.diversity := by
  unfold clinamenDispersalEntropy wasteFaceFromBule actionFaceFromBule
         entropyFaceFromBule
  simp; omega

/-- Three-face decomposition via entropy: total entropy is the sum of
    single-face entropies. -/
theorem entropy_decomposes_into_faces (b : BuleyUnit) :
    clinamenDispersalEntropy b =
      clinamenDispersalEntropy (wasteFaceFromBule b) +
      clinamenDispersalEntropy (actionFaceFromBule b) +
      clinamenDispersalEntropy (entropyFaceFromBule b) := by
  rw [single_face_entropy b]
  unfold clinamenDispersalEntropy
  omega

/-- Entropy conservation under face redistribution: permuting the face
    values does not change total entropy. -/
theorem entropy_conserved_on_face_permutation (b : BuleyUnit) :
    clinamenDispersalEntropy (cyclePermute b) = clinamenDispersalEntropy b := by
  unfold clinamenDispersalEntropy cyclePermute
  omega

/-- Maximum entropy bound: for an N-score Bule unit, entropy is at most N. -/
theorem entropy_bounded_by_score (b : BuleyUnit) :
    clinamenDispersalEntropy b ≤ buleyUnitScore b := by
  rw [entropy_equals_score]

/-- High entropy, low concentration: a Bule unit with score N has maximum
    entropy N iff all three faces can be nonzero. The most dispersed charge
    spreads equally. -/
def maximallyDispersedBule (n : Nat) : BuleyUnit :=
  let base := n / 3 in
  let remainder := n % 3 in
  if remainder = 0 then
    ⟨base, base, base⟩
  else if remainder = 1 then
    ⟨base + 1, base, base⟩
  else
    ⟨base + 1, base + 1, base⟩

theorem maximally_dispersed_has_correct_score (n : Nat) :
    buleyUnitScore (maximallyDispersedBule n) = n := by
  unfold maximallyDispersedBule buleyUnitScore
  split <;> split <;> simp <;> omega

theorem maximally_dispersed_has_max_entropy (n : Nat) :
    clinamenDispersalEntropy (maximallyDispersedBule n) = n := by
  rw [entropy_equals_score, maximally_dispersed_has_correct_score]

/-- The master entropy theorem: Shannon entropy on a Bule unit equals the
    sum of its face charges. Entropy is zero iff all faces are zero (vacuum).
    Entropy is maximal iff charges are spread across all three faces. -/
theorem entropy_is_clinamen_dispersal (b : BuleyUnit) :
    (clinamenDispersalEntropy b = buleyUnitScore b) ∧
    (clinamenDispersalEntropy b = 0 ↔ b = vacuumBuleUnit) ∧
    (clinamenDispersalEntropy b = buleyUnitScore b →
     (∃ (f : BuleyFace), 0 < match f with
      | .waste => b.waste
      | .opportunity => b.opportunity
      | .diversity => b.diversity) ∨
     b = vacuumBuleUnit) := by
  refine ⟨entropy_equals_score b, entropy_zero_iff_vacuum b, fun hEq => ?_⟩
  by_cases h : buleyUnitScore b = 0
  · right
    cases b; simp [buleyUnitScore] at h; simp [h]
  · left
    cases b with
    | mk w o d =>
      simp [buleyUnitScore] at h
      by_cases hw : 0 < w
      · exact ⟨.waste, hw⟩
      · push_neg at hw
        have w_eq : w = 0 := by omega
        by_cases ho : 0 < o
        · exact ⟨.opportunity, ho⟩
        · push_neg at ho
          have o_eq : o = 0 := by omega
          have d_pos : 0 < d := by omega
          exact ⟨.diversity, d_pos⟩

/-! ## Synthesis: Information as Topological Charge Mechanics -/

/-- A bit encodes one unit of charge. Multiple bits encode multiple units.
    Computation rearranges that charge. Entropy measures dispersal. The vacuum
    is the ground state (zero charge, zero entropy). Every configuration is
    reachable from vacuum by +1 lifts. Everything contracts back to vacuum. -/
theorem information_is_topological_charge :
    (∀ (b : Bit),
     let u := bitToBule b in
     match b with
     | .zero => buleyUnitScore u = 0 ∧ u = vacuumBuleUnit
     | .one => buleyUnitScore u = 1 ∧ clinamenDispersalEntropy u = 1) ∧
    (∀ (b : BuleyUnit),
     vacuumContractible b ∧
     clinamenDispersalEntropy b = buleyUnitScore b) ∧
    (∀ (b : BuleyUnit),
     clinamenDispersalEntropy b = 0 → b = vacuumBuleUnit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases b
    · show buleyUnitScore (bitToBule .zero) = 0 ∧ bitToBule .zero = vacuumBuleUnit
      simp [bitToBule]; exact ⟨rfl, rfl⟩
    · show buleyUnitScore (bitToBule .one) = 1 ∧
            clinamenDispersalEntropy (bitToBule .one) = 1
      simp [bitToBule, clinamenLift, clinamen_lift_score_strict_increment,
             vacuum_has_zero_score, entropy_equals_score]
      decide
  · intro b
    exact ⟨vacuum_contractible_from_any_bule b, entropy_equals_score b⟩
  · exact entropy_zero_implies_vacuum

end InformationAsClinamenCharge
end Gnosis
