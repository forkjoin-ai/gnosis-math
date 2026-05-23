import Init
import Gnosis.FiniteDynamicsCore
import Gnosis.AeonNoise
import Gnosis.ErgodicCutoffDuality
import Gnosis.ErgodicCutoffCycleType

/-!
# FiniteDynamicsUnification — the tie, demonstrated not asserted

The hypothesis under test: the ergodic-cutoff / antitheorem work ties together the
contrarian formalizations. The honest, kernel-checkable form of that hypothesis:

> Most contrarian dynamics modules are *instances* of one shared core
> (`Gnosis/FiniteDynamicsCore.lean`): a finite self-map with a period/order
> (`period_dvd`), an observable conserved across a cycle (`returns_conserves`), or a
> monovariant that dissipates to an absorbing state (`dissipative_not_periodic`); and the
> *refutation* half of each is one of two antitheorem schemas (`separates`,
> `not_forced_by_witness`).

This module is the demonstration. It re-derives, *through the shared core*, headline facts
that other modules proved ad hoc:

* `clock` period `n` — the substrate of `DiscreteClosedTimelikeStep` and the `AeonTwelve*` clocks;
* `catMod m` order (4 at `m=3`, 10 at `m=5`) — the content of `ArnoldCatMapOrder5`;
* the Collatz `{1,2,4}` absorbing 3-cycle — the content of `CollatzOneTwoFourBraid`.

And it produces *new* antitheorems from the schema:

* `out_shuffle_ne_clock`, `catMod3_ne_catMod5` — `separates` (a differing invariant
  refutes an identity), same shape as `actions_are_not_conjugate`;
* `period_twelve_does_not_force_period_ten` — `not_forced_by_witness`, the shape behind the
  `contrarian` non-forcing queue antitheorems.

## What this does and does not claim

It claims, and proves, that the **dynamics sub-family** shares one core. It does **not**
claim the whole `Gnosis/Contrarian/` corpus reduces to it: most of those files are
*inversions* (`chaos_is_order`, `efficiency_is_fragility`, `death_limit_enables_vitality`)
that, by the `Contrarian/README` design, are thin bounded consequences of a structure
field — they share the anti-theory *stance* (`ANTI_THEORY_MANIFESTO.md`), not this core.

**Falsifiable conjecture (anti-theory layer).** Every `Gnosis/Contrarian/` headline factors
as exactly one of: (i) a `separates` separation, (ii) a `not_forced_by_witness` non-forcing,
(iii) a monovariant inversion `threshold → opposite` (modus ponens on a field), or
(iv) a `period_dvd` / `returns_conserves` / dissipation dynamics fact. *Falsifying test:*
exhibit one Contrarian module whose central theorem fits none of (i)–(iv).

*Tested and closed.* The falsifying pass (50/50 files, 2026-05-22) found no escapee, but
showed `separates` was overloaded. The refinement and **closure** live in
[`Gnosis/ContrarianSchemaClosure.lean`](Gnosis/ContrarianSchemaClosure.lean): two more schemas
`Equates` (`=`) and `Dominates` (`<`), and the kernel-checked, *axiom-free* exhaustiveness —
`comparison_verdict_complete` (every measure comparison is `<`/`=`/`>`, trichotomy) and
`forces_or_not_forced` (every universal claim holds or has a witness). The corpus is the
finite image of a five-verdict basis on decidable measures.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace FiniteDynamicsUnification

open Gnosis.AeonNoise
open Gnosis.ErgodicCutoffDuality
open Gnosis.ErgodicCutoffCycleType
open Gnosis.FiniteDynamicsCore

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The discrete clock — period n (substrate of DiscreteClosedTimelikeStep)
-- ═══════════════════════════════════════════════════════════════════════

/-- The discrete +1 clock modulo `n`. -/
def clock (n i : Nat) : Nat := (i + 1) % n

/-- The 12-hour carrier. -/
def clockCarrier : List Nat := List.range 12

theorem clock_carrier_closed : ∀ i ∈ clockCarrier, clock 12 i ∈ clockCarrier := by decide

theorem clock_returns_all_12 : ReturnsAll (clock 12) clockCarrier 12 := by
  unfold ReturnsAll; decide

theorem clock_no_small_period :
    ∀ d, d < 12 → 0 < d → ¬ ReturnsAll (clock 12) clockCarrier d := by
  unfold ReturnsAll; decide

/-- The clock's periods are exactly the multiples of 12 — order exactly 12, re-derived
    through the shared `period_dvd`. -/
theorem clock_period_iff (T : Nat) :
    ReturnsAll (clock 12) clockCarrier T ↔ 12 ∣ T := by
  constructor
  · exact period_dvd (clock 12) clockCarrier 12 (by decide) clock_carrier_closed
      clock_returns_all_12 clock_no_small_period T
  · intro h
    exact returnsAll_of_dvd (clock 12) clockCarrier 12 T h clock_returns_all_12

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Arnold cat map at modulus 3 — order 4 (content of ArnoldCatMapOrder5)
-- ═══════════════════════════════════════════════════════════════════════

/-- The Arnold cat map modulo `m`. `catMod 5` is definitionally `aeonCatMap`. -/
def catMod (m : Nat) (p : Nat × Nat) : Nat × Nat :=
  ((2 * p.1 + p.2) % m, (p.1 + p.2) % m)

/-- The 9-coordinate carrier `(Z/3)²`. -/
def catCarrier3 : List (Nat × Nat) :=
  [ (0,0),(0,1),(0,2), (1,0),(1,1),(1,2), (2,0),(2,1),(2,2) ]

theorem catMod3_carrier_closed : ∀ p ∈ catCarrier3, catMod 3 p ∈ catCarrier3 := by decide

theorem catMod3_returns_all_4 : ReturnsAll (catMod 3) catCarrier3 4 := by
  unfold ReturnsAll; decide

theorem catMod3_no_small_period :
    ∀ d, d < 4 → 0 < d → ¬ ReturnsAll (catMod 3) catCarrier3 d := by
  unfold ReturnsAll; decide

/-- Cat map mod 3 has order exactly 4 (periods = multiples of 4), re-derived through the
    shared `period_dvd`. Same map family, different modulus, different order than mod 5's 10. -/
theorem catMod3_period_iff (T : Nat) :
    ReturnsAll (catMod 3) catCarrier3 T ↔ 4 ∣ T := by
  constructor
  · exact period_dvd (catMod 3) catCarrier3 4 (by decide) catMod3_carrier_closed
      catMod3_returns_all_4 catMod3_no_small_period T
  · intro h
    exact returnsAll_of_dvd (catMod 3) catCarrier3 4 T h catMod3_returns_all_4

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Collatz {1,2,4} absorbing cycle (content of CollatzOneTwoFourBraid)
-- ═══════════════════════════════════════════════════════════════════════

/-- The terminal Collatz orbit `1 → 4 → 2 → 1`. -/
def ctri (i : Nat) : Nat := if i = 1 then 4 else if i = 4 then 2 else if i = 2 then 1 else i

def ctriCarrier : List Nat := [1, 2, 4]

theorem ctri_carrier_closed : ∀ i ∈ ctriCarrier, ctri i ∈ ctriCarrier := by decide

theorem ctri_returns_all_3 : ReturnsAll ctri ctriCarrier 3 := by
  unfold ReturnsAll; decide

theorem ctri_no_small_period :
    ∀ d, d < 3 → 0 < d → ¬ ReturnsAll ctri ctriCarrier d := by
  unfold ReturnsAll; decide

/-- The Collatz terminal cycle has order exactly 3, re-derived through `period_dvd`. -/
theorem ctri_period_iff (T : Nat) :
    ReturnsAll ctri ctriCarrier T ↔ 3 ∣ T := by
  constructor
  · exact period_dvd ctri ctriCarrier 3 (by decide) ctri_carrier_closed
      ctri_returns_all_3 ctri_no_small_period T
  · intro h
    exact returnsAll_of_dvd ctri ctriCarrier 3 T h ctri_returns_all_3

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Antitheorems from the shared schemas
-- ═══════════════════════════════════════════════════════════════════════

/-- **Separation antitheorem.** On the same 12 cards, the perfect out-shuffle (order 10)
    and the 12-hour clock (order 12) are different permutations: the clock has no fixed
    point, the out-shuffle has two. An instance of `separates`. -/
theorem out_shuffle_ne_clock : outShuffle12 ≠ clock 12 :=
  separates (fun f => countFixedBy f shuffleCarrier 1)
    (a := outShuffle12) (b := clock 12) (by decide)

/-- **Separation antitheorem.** On the same `(Z/5)²` grid, the cat map mod 3 and mod 5 are
    different dynamics: `f²` fixes 1 point under mod 3 but 5 under mod 5. An instance of
    `separates` — same family, different modulus, refuted as identical. -/
theorem catMod3_ne_catMod5 : catMod 3 ≠ catMod 5 :=
  separates (fun f => countFixedBy f catCarrier 2)
    (a := catMod 3) (b := catMod 5) (by decide)

/-- **Non-forcing antitheorem.** Returning after 12 ticks does not force returning after
    10: the clock witnesses period 12 while failing period 10. An instance of
    `not_forced_by_witness` — the shape behind the contrarian non-forcing queue results. -/
theorem period_twelve_does_not_force_period_ten :
    ¬ (∀ f : Nat → Nat, ReturnsAll f clockCarrier 12 → ReturnsAll f clockCarrier 10) :=
  not_forced_by_witness
    (fun f => ReturnsAll f clockCarrier 12)
    (fun f => ReturnsAll f clockCarrier 10)
    (clock 12)
    clock_returns_all_12
    (by unfold ReturnsAll; decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Master — the dynamics sub-family on one core
-- ═══════════════════════════════════════════════════════════════════════

/--
One core, five systems: clock (order 12), cat mod 3 (order 4), cat mod 5 / out-shuffle
(order 10, from `ErgodicCutoffCycleType`), Collatz terminal cycle (order 3) — each an
instance of `period_dvd` — plus three antitheorems from the two shared schemas.
-/
theorem finite_dynamics_unification_master :
    (∀ T, ReturnsAll (clock 12) clockCarrier T ↔ 12 ∣ T) ∧
    (∀ T, ReturnsAll (catMod 3) catCarrier3 T ↔ 4 ∣ T) ∧
    (∀ T, ReturnsAll ctri ctriCarrier T ↔ 3 ∣ T) ∧
    (∀ T, ReturnsAll aeonCatMap catCarrier T ↔ 10 ∣ T) ∧
    outShuffle12 ≠ clock 12 ∧
    catMod 3 ≠ catMod 5 ∧
    ¬ (∀ f : Nat → Nat, ReturnsAll f clockCarrier 12 → ReturnsAll f clockCarrier 10) :=
  ⟨clock_period_iff, catMod3_period_iff, ctri_period_iff, cat_period_iff,
    out_shuffle_ne_clock, catMod3_ne_catMod5, period_twelve_does_not_force_period_ten⟩

end FiniteDynamicsUnification
end Gnosis
