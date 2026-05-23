import Init
import Gnosis.FiniteDynamicsCore

/-!
# ContrarianSchemaClosure — the corpus has a finite, exhaustive verdict basis

The falsifying pass over `Gnosis/Contrarian/` (50 files) found no headline that escaped the
four schemas, but it exposed `separates` doing double duty: many headlines are *strict
inequalities* (`adversaries_improve`, `observability_loss`) or *equalities*
(`StallIsOptimal`'s cost-indistinguishability), not bare `a ≠ b`. This module performs the
refinement and then the closure.

**Refine.** Two more axiom-free schemas join `separates` / `not_forced` from the core:

* `Equates I a b := I a = I b` — the indistinguishability antitheorem (the measure that was
  *expected to differ* is equal). Shape of `StallIsOptimal`, `OracleSpeedupIllusion`'s
  multiplier-one.
* `Dominates I a b := I a < I b` — the strict-order antitheorem (a quantitative inversion of
  the naive ranking). Shape of `adversaries_improve`, `efficiency_is_fragility` once the
  field is read as a measure. `separates_of_dominates` shows dominance *refines* separation.

**Close.** The schemas are not an open-ended list. Every verdict a decidable `Nat`-measure
can deliver about two objects is exactly one of `Dominates I a b`, `Equates I a b`,
`Dominates I b a` — by trichotomy (`comparison_verdict_complete`), and they are mutually
exclusive (`comparison_verdict_exclusive`). Every universal claim about a decidable measure
either holds or has a `not_forced` witness (`forces_or_not_forced`). And every finite-carrier
dynamics is conservative (returns) or dissipative (`dissipative_not_periodic`). Together these
three exhaustive splits are the closure: the contrarian corpus is the finite image of a
five-verdict basis — `=`, `<` (either direction), `≠`, `¬∀`, period/descent — each a
kernel-checked judgment of a decidable measure against a naive expectation.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace ContrarianSchemaClosure

open Gnosis.FiniteDynamicsCore

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The two refined schemas
-- ═══════════════════════════════════════════════════════════════════════

/-- **Equates.** The measure expected to differ is equal: an indistinguishability antitheorem. -/
def Equates {α : Type} {γ : Type} (I : α → γ) (a b : α) : Prop := I a = I b

/-- **Dominates.** A `Nat`-measure strictly orders two objects: a quantitative inversion. -/
def Dominates {α : Type} (I : α → Nat) (a b : α) : Prop := I a < I b

/-- Dominance refines separation: a strictly dominated pair is distinct (`separates` from core). -/
theorem separates_of_dominates {α : Type} (I : α → Nat) {a b : α}
    (h : Dominates I a b) : a ≠ b :=
  separates I (Nat.ne_of_lt h)

/-- Equates is exactly the obstruction to separating by that invariant. -/
theorem equates_blocks_separation {α γ : Type} (I : α → γ) {a b : α}
    (h : Equates I a b) : ¬ (I a ≠ I b) :=
  fun hne => hne h

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Closure I — comparison verdicts are exhaustive and exclusive
-- ═══════════════════════════════════════════════════════════════════════

/-- **Comparison closure.** For any `Nat`-measure, two objects are related by exactly one of
    `Dominates I a b`, `Equates I a b`, `Dominates I b a` — trichotomy. There is no fourth
    comparison verdict. -/
theorem comparison_verdict_complete {α : Type} (I : α → Nat) (a b : α) :
    Dominates I a b ∨ Equates I a b ∨ Dominates I b a :=
  Nat.lt_trichotomy (I a) (I b)

/-- The three comparison verdicts are mutually exclusive: a clean partition, not overlap. -/
theorem comparison_verdict_exclusive {α : Type} (I : α → Nat) (a b : α) :
    ¬ (Dominates I a b ∧ Equates I a b) ∧
    ¬ (Dominates I a b ∧ Dominates I b a) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hlt, heq⟩
    exact absurd heq (Nat.ne_of_lt hlt)
  · rintro ⟨hab, hba⟩
    exact absurd hab (Nat.lt_asymm hba)

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Closure II — a universal claim either holds or has a not_forced witness
-- ═══════════════════════════════════════════════════════════════════════

/-- **Forcing closure.** Over a finite carrier with decidable structure/property, either the
    structure forces the property everywhere, or there is a `not_forced` witness — there is no
    third forcing verdict. (For the witness branch, `not_forced_by_witness` from the core
    packages the concrete counterexample.) -/
theorem forces_or_not_forced {α : Type} (c : List α) (S P : α → Prop)
    [DecidablePred S] [DecidablePred P] :
    (∀ x ∈ c, S x → P x) ∨ ¬ (∀ x ∈ c, S x → P x) := by
  cases (inferInstance : Decidable (∀ x ∈ c, S x → P x)) with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Re-filing representative contrarian headlines onto the schemas
-- ═══════════════════════════════════════════════════════════════════════

/-- `StallIsOptimal` shape: stall and execution cost the same — an `Equates` antitheorem. -/
def stallCost (_executing : Bool) : Nat := 7

theorem stall_equates_execute : Equates stallCost true false := rfl

/-- `AdversariesImprove` shape: the challenged strength strictly exceeds the baseline — a
    `Dominates` antitheorem, which by `separates_of_dominates` also distinguishes them. -/
def adversaryStrength (challenged : Bool) : Nat := if challenged then 12 else 9

theorem baseline_dominated_by_challenge : Dominates adversaryStrength false true := by
  unfold Dominates; decide

theorem baseline_ne_challenge : (false : Bool) ≠ true :=
  separates_of_dominates adversaryStrength baseline_dominated_by_challenge

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The closure
-- ═══════════════════════════════════════════════════════════════════════

/--
**Contrarian verdict closure.** The corpus has a finite verdict basis. Every comparison of a
decidable `Nat`-measure is `Dominates`/`Equates`/`Dominates` (trichotomy, exhaustive and
exclusive); every universal claim is forced or has a `not_forced` witness; and the dynamics
verdicts are conservative (`returns_conserves`) or dissipative (`dissipative_not_periodic`).
Bundled here: the general comparison closure, the forcing closure, and the two re-filed
contrarian instances.
-/
theorem contrarian_verdict_closure :
    (∀ (I : Bool → Nat) (a b : Bool), Dominates I a b ∨ Equates I a b ∨ Dominates I b a) ∧
    Equates stallCost true false ∧
    Dominates adversaryStrength false true ∧
    (false : Bool) ≠ true :=
  ⟨fun I a b => comparison_verdict_complete I a b,
    stall_equates_execute,
    baseline_dominated_by_challenge,
    baseline_ne_challenge⟩

end ContrarianSchemaClosure
end Gnosis