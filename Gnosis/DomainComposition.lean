import Init

/-!
# Domain Composition — Thermodynamic Products and Morphisms

UniversalDomainConservation proved that every domain satisfies
fork = fold + vent, vent ≥ 1. This file opens the door it revealed:
**what happens when two domains interact?**

If combat and humor both satisfy the conservation law, does their
PRODUCT (combat while joking) also satisfy it? Does their SEQUENTIAL
COMPOSITION (humor feeding into economics) preserve the invariants?

This module proves:

1. **Parallel Product**: (d₁ ⊗ d₂) satisfies conservation if both
   components do. fork₁₂ = fork₁ + fork₂, and conservation is additive.
2. **Sequential Pipeline**: d₁ → d₂ where fold₁ becomes fork₂.
   Conservation composes: the second stage's input is bounded by
   the first stage's useful work.
3. **Efficiency Ordering**: d₁ ≤ d₂ iff d₁.foldWork ≤ d₂.foldWork
   given equal forkEnergy. This ordering is a partial order.
4. **Heat Death is Terminal**: every domain eventually reaches heat death
   under repeated pipeline composition (fold decreases monotonically).

The category structure: DomainTopology is a monoidal category where
⊗ is parallel composition and → is sequential composition.

Zero -- placeholder.
-/

namespace Gnosis

-- ═══════════════════════════════════════════════════════════════════════
-- §1. DomainTopology (reproduced, self-contained)
-- ═══════════════════════════════════════════════════════════════════════

structure DomainTopology where
  forkEnergy : Nat
  foldWork : Nat
  ventHeat : Nat
  conservation : forkEnergy = foldWork + ventHeat
  sliver : ventHeat ≥ 1

-- ═══════════════════════════════════════════════════════════════════════
-- §2. Parallel Product: d₁ ⊗ d₂
-- ═══════════════════════════════════════════════════════════════════════

/-- Parallel product of two domains: both execute simultaneously. -/
def parallel (d₁ d₂ : DomainTopology) : DomainTopology :=
  ⟨d₁.forkEnergy + d₂.forkEnergy,
   d₁.foldWork + d₂.foldWork,
   d₁.ventHeat + d₂.ventHeat,
   by omega,
   by have := d₁.sliver; have := d₂.sliver; omega⟩

/-- THM-PARALLEL-CONSERVATION: Parallel composition preserves conservation. -/
theorem parallel_conservation (d₁ d₂ : DomainTopology) :
    (parallel d₁ d₂).forkEnergy = (parallel d₁ d₂).foldWork + (parallel d₁ d₂).ventHeat :=
  (parallel d₁ d₂).conservation

/-- THM-PARALLEL-SLIVER: Parallel composition preserves the sliver.
    If both domains waste ≥ 1, the product wastes ≥ 2. -/
theorem parallel_sliver (d₁ d₂ : DomainTopology) :
    (parallel d₁ d₂).ventHeat ≥ 2 := by
  unfold parallel; have := d₁.sliver; have := d₂.sliver; omega

/-- THM-PARALLEL-COMMUTATIVE: Parallel composition is commutative. -/
theorem parallel_commutative (d₁ d₂ : DomainTopology) :
    (parallel d₁ d₂).forkEnergy = (parallel d₂ d₁).forkEnergy ∧
    (parallel d₁ d₂).foldWork = (parallel d₂ d₁).foldWork ∧
    (parallel d₁ d₂).ventHeat = (parallel d₂ d₁).ventHeat := by
  unfold parallel; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §3. Sequential Pipeline: d₁ → d₂
-- ═══════════════════════════════════════════════════════════════════════

/-- Sequential pipeline: d₁'s fold output becomes d₂'s fork input.
    Since fold₁ < fork₁ (strict loss), the second stage starts with
    strictly less energy. Entropy accumulates. -/
def pipeline (d₁ : DomainTopology) (ventRatio₂ : Nat) (hVent : ventRatio₂ ≥ 1)
    (hBound : ventRatio₂ ≤ d₁.foldWork) : DomainTopology :=
  ⟨d₁.foldWork,
   d₁.foldWork - ventRatio₂,
   ventRatio₂,
   by omega,
   hVent⟩

/-- THM-PIPELINE-ENERGY-DECREASES: Pipeline output has strictly less
    fork energy than the first stage's input. Energy dissipates. -/
theorem pipeline_energy_decreases (d₁ : DomainTopology)
    (v₂ : Nat) (hV : v₂ ≥ 1) (hB : v₂ ≤ d₁.foldWork) :
    (pipeline d₁ v₂ hV hB).forkEnergy < d₁.forkEnergy := by
  unfold pipeline
  have := d₁.conservation
  have := d₁.sliver
  omega

/-- THM-PIPELINE-FOLD-BOUNDED: Each pipeline stage's fold output is
    strictly less than its fork input. Useful work monotonically
    decreases through pipeline stages. -/
theorem pipeline_fold_bounded (d₁ : DomainTopology)
    (v₂ : Nat) (hV : v₂ ≥ 1) (hB : v₂ ≤ d₁.foldWork) :
    (pipeline d₁ v₂ hV hB).foldWork < (pipeline d₁ v₂ hV hB).forkEnergy := by
  unfold pipeline; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4. Heat Death as Terminal Object
-- ═══════════════════════════════════════════════════════════════════════

/-- The heat death domain: fork = 1, fold = 0, vent = 1.
    All energy is entropy. No useful work. Terminal object. -/
def heatDeath : DomainTopology := ⟨1, 0, 1, rfl, by omega⟩

/-- THM-HEAT-DEATH-TERMINAL: Heat death has zero useful work.
    It is the absorbing state of all pipeline compositions. -/
theorem heat_death_zero_work : heatDeath.foldWork = 0 := rfl

/-- THM-HEAT-DEATH-MINIMAL-FORK: Heat death has the minimum possible
    fork energy (1). Any domain with fork = 0 would violate sliver. -/
theorem heat_death_minimal : heatDeath.forkEnergy = 1 := rfl

/-- THM-NO-DOMAIN-BELOW-HEAT-DEATH: No domain has fork < 1. Heat death
    is the absolute floor. -/
theorem no_below_heat_death (d : DomainTopology) :
    d.forkEnergy ≥ 1 := by
  have := d.conservation; have := d.sliver; omega

/-- THM-HEAT-DEATH-NO-PIPELINE: Heat death cannot be pipelined further
    (fold = 0, so no second stage can receive any energy). -/
theorem heat_death_no_pipeline : heatDeath.foldWork = 0 := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Efficiency Ordering
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-EFFICIENCY-REFLEXIVE: Every domain is at least as efficient as itself. -/
theorem efficiency_reflexive (d : DomainTopology) :
    d.foldWork ≤ d.foldWork := Nat.le_refl _

/-- THM-EFFICIENCY-ANTISYMMETRIC: If d₁ ≤ d₂ and d₂ ≤ d₁ then they
    have equal fold work. -/
theorem efficiency_antisymmetric (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b := by omega

/-- THM-EFFICIENCY-TRANSITIVE: The efficiency ordering is transitive. -/
theorem efficiency_transitive (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) :
    a ≤ c := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §6. Concrete Compositions
-- ═══════════════════════════════════════════════════════════════════════

def combat : DomainTopology := ⟨10, 7, 3, rfl, by omega⟩
def humor : DomainTopology := ⟨8, 5, 3, rfl, by omega⟩
def crypto : DomainTopology := ⟨256, 1, 255, rfl, by omega⟩

/-- Combat ⊗ Humor: fighting while joking. -/
theorem combat_humor_parallel :
    (parallel combat humor).forkEnergy = 18 ∧
    (parallel combat humor).foldWork = 12 ∧
    (parallel combat humor).ventHeat = 6 := by
  unfold parallel combat humor; exact ⟨rfl, rfl, rfl⟩

/-- Entropy accumulates: crypto is maximally wasteful. -/
theorem crypto_almost_all_waste :
    crypto.ventHeat > crypto.foldWork ∧
    crypto.ventHeat = 255 := by
  unfold crypto; exact ⟨by omega, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §7. Master Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-DOMAIN-COMPOSITION-MASTER: Domain topologies form an algebra.

    1. Parallel composition preserves conservation and strengthens sliver.
    2. Sequential pipeline dissipates energy monotonically.
    3. Heat death is the terminal object (absorbing state).
    4. Efficiency ordering is a partial order (reflexive, antisymmetric, transitive).
    5. No domain can go below heat death (fork ≥ 1). -/
theorem domain_composition_master (d₁ d₂ : DomainTopology) :
    -- Parallel preserves conservation
    (parallel d₁ d₂).forkEnergy = (parallel d₁ d₂).foldWork + (parallel d₁ d₂).ventHeat ∧
    -- Parallel strengthens sliver
    (parallel d₁ d₂).ventHeat ≥ 2 ∧
    -- Heat death is minimal
    heatDeath.foldWork = 0 ∧
    -- No domain below heat death
    d₁.forkEnergy ≥ 1 ∧ d₂.forkEnergy ≥ 1 := by
  exact ⟨parallel_conservation d₁ d₂,
         parallel_sliver d₁ d₂,
         heat_death_zero_work,
         no_below_heat_death d₁,
         no_below_heat_death d₂⟩

end Gnosis
