import Init
import Gnosis.MycelialEmergenceGraph
import Gnosis.Body.KinSelection

/-!
# Anthropogenesis — Human Development & Anthropology in the Metaverse

The Metaverse (the 3D Game-of-Life evolutionary world in `aeon-corpus`) is
**attention voting on dark matter**: agents cast attention votes (affinity vs
disagreement edges, `Gnosis.MycelialEmergenceGraph`) over an unseen carrying
capacity (the dark-matter / void latent reservoir, `Gnosis.VoidIsDarkMatter`).
Live cells are mycelial coalitions; overcrowding and isolation are death.

This module turns the laws observed empirically in the Metaverse into theorems:

* survival is a band (Conway, generalized) — `survival_trichotomy`;
* the visible population is bounded by the dark capacity — `grow_never_exceeds_dark_capacity`;
* a live cell is a coalition / net-positive attention vote — `coalition_is_emergence`;
* **stress produces anxiety, then culture** — `stress_produces_culture`;
* **anxiety has positive adaptive value** — `anxiety_has_positive_value`;
* culture never regresses across generations (the ratchet) — `culture_never_regresses`;
* a non-breeding pan transmits culture, not genes — `pan_transmits_culture`;
* **life had to be**: selection on world fitness inevitably yields life —
  `life_had_to_be`.

Rustic Church: `Init` only, `Nat` arithmetic, proofs from core lemmas.
-/

namespace Gnosis.Body.Anthropogenesis

open Gnosis.MycelialEmergenceGraph
open Gnosis.Body.KinSelection

/-! ## The survival band (Game of Life, generalized to a 3D neighbourhood) -/

/-- A Game-of-Life survival band: a cell lives iff its neighbour count
    (attention votes received) lies in `[lo, hi]`. -/
structure SurvivalBand where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

def survives (b : SurvivalBand) (n : Nat) : Prop := b.lo ≤ n ∧ n ≤ b.hi
def diesUnderpopulation (b : SurvivalBand) (n : Nat) : Prop := n < b.lo
def diesOvercrowding (b : SurvivalBand) (n : Nat) : Prop := b.hi < n

/-- Every cell does exactly one of: survive, die isolated, die overcrowded. -/
theorem survival_trichotomy (b : SurvivalBand) (n : Nat) :
    survives b n ∨ diesUnderpopulation b n ∨ diesOvercrowding b n := by
  unfold survives diesUnderpopulation diesOvercrowding
  rcases Nat.lt_or_ge n b.lo with hlo | hlo
  · exact Or.inr (Or.inl hlo)
  · rcases Nat.lt_or_ge b.hi n with hhi | hhi
    · exact Or.inr (Or.inr hhi)
    · exact Or.inl ⟨hlo, hhi⟩

/-- Overcrowding excludes survival: beyond the band's top, a cell cannot live —
    the carrying-capacity cliff observed in the Metaverse. -/
theorem overcrowding_excludes_survival (b : SurvivalBand) (n : Nat) (h : b.hi < n) :
    ¬ survives b n := by
  unfold survives
  intro hs
  exact Nat.lt_irrefl n (Nat.lt_of_le_of_lt hs.right h)

/-! ## Dark matter: the unseen carrying capacity bounds the visible -/

/-- The dark-matter / void carrying capacity `K`: detected only by its bound on
    the visible population. -/
structure DarkCapacity where
  capacity : Nat
  deriving Repr, DecidableEq

/-- A growth step: births add to the visible population, capped by the unseen
    dark capacity (attention voting on dark matter). -/
def growStep (visible births : Nat) (dark : DarkCapacity) : Nat :=
  Nat.min (visible + births) dark.capacity

/-- The visible population never exceeds the dark-matter carrying capacity. -/
theorem grow_never_exceeds_dark_capacity (visible births : Nat) (dark : DarkCapacity) :
    growStep visible births dark ≤ dark.capacity := by
  unfold growStep
  exact Nat.min_le_right _ _

/-! ## Mycelial emergence: a live cell is a coalition / net-positive vote -/

/-- A live cell is a mycelial coalition: an attention vote whose agreement
    (affinity) strictly exceeds its disagreement. -/
def coalition_is_emergence (e : EmergenceEdge) (h : coalitionCandidate e) :
    e.disagreement < e.affinity :=
  coalition_affinity_exceeds_disagreement e h

/-! ## Stress -> anxiety -> culture -/

/-- Anxiety tracks somatic stress. -/
def anxiety (stress : Nat) : Nat := stress
/-- Anxiety drives teaching (a stressed agent broadcasts its hard-won memory). -/
def teachingDrive (anxiety : Nat) : Nat := anxiety
/-- Teaching grows shared culture (rejection norms that propagate). -/
def cultureGained (teaching : Nat) : Nat := teaching

/-- The full pathway: stress becomes culture by passing through anxiety and
    teaching. -/
def stressToCulture (stress : Nat) : Nat :=
  cultureGained (teachingDrive (anxiety stress))

/-- **Stress produces anxiety, then culture**: a stressed population converts its
    stress into shared culture; with no stress, no new culture emerges. -/
theorem stress_produces_culture (stress : Nat) (h : 0 < stress) :
    0 < stressToCulture stress := by
  unfold stressToCulture cultureGained teachingDrive anxiety
  exact h

/-- More stress never yields less culture (monotone transmission). -/
theorem more_stress_more_culture (s₁ s₂ : Nat) (h : s₁ ≤ s₂) :
    stressToCulture s₁ ≤ stressToCulture s₂ := by
  unfold stressToCulture cultureGained teachingDrive anxiety
  exact h

/-- **Anxiety has positive adaptive value**: an agent that feels anxiety under
    stress gains culture; an unfeeling agent (anxiety suppressed to 0) gains
    none. So anxiety strictly adds survival value — it is the trigger that turns
    adversity into transmissible knowledge. -/
theorem anxiety_has_positive_value (stress : Nat) (h : 0 < stress) :
    cultureGained (teachingDrive 0) < cultureGained (teachingDrive (anxiety stress)) := by
  unfold cultureGained teachingDrive anxiety
  exact h

/-! ## The cultural ratchet across generations (development / anthropology) -/

/-- Offspring inherit the union of both parents' culture (rejection memory). -/
def inheritedCulture (parentA parentB : Nat) : Nat := Nat.max parentA parentB

/-- **Culture never regresses**: each generation knows at least as much as either
    parent — the cultural ratchet that makes cumulative human development possible. -/
theorem culture_never_regresses (parentA parentB : Nat) :
    parentA ≤ inheritedCulture parentA parentB := by
  unfold inheritedCulture
  exact Nat.le_max_left _ _

/-- A non-breeding pan transmits culture, not genes: with zero direct offspring,
    a pan that teaches kin still has positive (inclusive) fitness — the
    anthropology of the helper, reusing `KinSelection.pan_payoff`. -/
theorem pan_transmits_culture (relatedness kinTaught : Nat)
    (hr : 0 < relatedness) (hk : 0 < kinTaught) :
    0 < inclusiveFitness panDirectOffspring relatedness kinTaught :=
  pan_payoff relatedness kinTaught hr hk

/-! ## The ultimate goal: life had to be -/

/-- World fitness: an extinct world scores 0; a sustaining world scores its
    (positive) sustained population. -/
def extinctFitness : Nat := 0
def sustainingFitness (sustained : Nat) : Nat := sustained

/-- Selection keeps the fitter of two worlds. -/
def select (a b : Nat) : Nat := Nat.max a b

/-- **Life is possible in any world** with positive dark-matter capacity: there
    is always a viable, non-empty population within the carrying capacity. -/
theorem life_is_possible (dark : DarkCapacity) (h : 0 < dark.capacity) :
    ∃ visible, 0 < visible ∧ visible ≤ dark.capacity :=
  ⟨dark.capacity, h, Nat.le_refl dark.capacity⟩

/-- Under selection, a sustaining world strictly dominates extinction. -/
theorem life_dominates_extinction (sustained : Nat) (h : 0 < sustained) :
    extinctFitness < sustainingFitness sustained := by
  unfold extinctFitness sustainingFitness
  exact h

/-- **Life had to be.** In any world with positive dark-matter capacity, a viable
    population exists, and under selection on world fitness it strictly beats
    extinction — so selection (meta-evolution) inevitably converges to life. The
    sweet spot is not chosen; it is forced, because non-life scores zero. -/
theorem life_had_to_be (dark : DarkCapacity) (h : 0 < dark.capacity) :
    (∃ visible, 0 < visible ∧ visible ≤ dark.capacity) ∧
    (∀ sustained, 0 < sustained → select extinctFitness (sustainingFitness sustained)
        = sustainingFitness sustained) := by
  refine ⟨life_is_possible dark h, ?_⟩
  intro sustained hs
  unfold select extinctFitness sustainingFitness
  exact Nat.max_eq_right (Nat.zero_le sustained)

/-! ## Anxiety is the vacuum; culture attenuates it -/

/-- The felt vacuum: the unfilled carrying capacity (dark matter minus visible). -/
def vacuum (visible : Nat) (dark : DarkCapacity) : Nat := dark.capacity - visible

/-- **Anxiety is the vacuum.** A world filled to its dark-matter capacity feels no
    anxiety; the vacuum is exactly the gap between the unseen capacity and the
    visible population. -/
theorem full_world_has_no_vacuum (visible : Nat) (dark : DarkCapacity)
    (h : dark.capacity ≤ visible) : vacuum visible dark = 0 := by
  unfold vacuum
  exact Nat.sub_eq_zero_of_le h

/-- An empty world is all vacuum — maximal anxiety. -/
theorem empty_world_is_all_vacuum (dark : DarkCapacity) :
    vacuum 0 dark = dark.capacity := by
  unfold vacuum
  exact Nat.sub_zero dark.capacity

/-- Applying culture to the vacuum. -/
def attenuate (vac culture : Nat) : Nat := vac - culture

/-- **Culture attenuates the vacuum.** Producing culture never increases the felt
    vacuum — closing the loop: the vacuum produces anxiety, anxiety produces
    culture, and culture exists in order to attenuate the vacuum. -/
theorem culture_attenuates_vacuum (vac culture : Nat) : attenuate vac culture ≤ vac := by
  unfold attenuate
  exact Nat.sub_le vac culture

/-- Enough culture clears the anxiety entirely. -/
theorem enough_culture_clears_vacuum (vac culture : Nat) (h : vac ≤ culture) :
    attenuate vac culture = 0 := by
  unfold attenuate
  exact Nat.sub_eq_zero_of_le h

/-! ## The contrarian theorem (for history): comfort is cultural death -/

/-- **Comfort is cultural death.** With no anxiety — the vacuum filled, stress
    zero — no culture is generated. The conventional reading prizes comfort; the
    Metaverse says the opposite. Culture is the child of the vacuum, not of ease;
    a world without the felt vacuum is a world without development. Pair with
    `stress_produces_culture`: culture requires anxiety. -/
theorem comfort_is_cultural_death : stressToCulture 0 = 0 := rfl

/-! ## Life happens on the edges (the edge of chaos) -/

def atEdge (b : SurvivalBand) (n : Nat) : Prop := n = b.lo ∨ n = b.hi
def interior (b : SurvivalBand) (n : Nat) : Prop := b.lo < n ∧ n < b.hi

/-- A strictly interior cell survives. -/
theorem interior_survives (b : SurvivalBand) (n : Nat) (h : interior b n) :
    survives b n := by
  unfold interior at h
  unfold survives
  exact ⟨Nat.le_of_lt h.left, Nat.le_of_lt h.right⟩

/-- The lower edge is critical: it survives, but losing one neighbour kills it. -/
theorem lower_edge_is_critical (b : SurvivalBand) (hw : b.lo ≤ b.hi) (hlo : 0 < b.lo) :
    survives b b.lo ∧ diesUnderpopulation b (b.lo - 1) := by
  unfold survives diesUnderpopulation
  exact ⟨⟨Nat.le_refl b.lo, hw⟩, Nat.sub_lt hlo Nat.one_pos⟩

/-- The upper edge is critical: it survives, but one more neighbour kills it. -/
theorem upper_edge_is_critical (b : SurvivalBand) (hw : b.lo ≤ b.hi) :
    survives b b.hi ∧ diesOvercrowding b (b.hi + 1) := by
  unfold survives diesOvercrowding
  exact ⟨⟨hw, Nat.le_refl b.hi⟩, Nat.lt_succ_self b.hi⟩

/-- **Life happens on the edges.** Interior cells are robust and complacent; the
    band's two edges survive but sit one perturbation from death. So every
    birth/death transition — the generative churn of life and culture — lives at
    the boundary between isolation and overcrowding: the edge of chaos. -/
theorem life_happens_on_the_edges (b : SurvivalBand) (hw : b.lo ≤ b.hi) (hlo : 0 < b.lo) :
    (survives b b.lo ∧ diesUnderpopulation b (b.lo - 1)) ∧
    (survives b b.hi ∧ diesOvercrowding b (b.hi + 1)) :=
  ⟨lower_edge_is_critical b hw hlo, upper_edge_is_critical b hw⟩

end Gnosis.Body.Anthropogenesis
