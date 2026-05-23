import Gnosis.NullIsTheZero

/-!
# ClinamenInfrathin — the clinamen as the infrathin moment of the first `+1`

Two old names for one event meet at a single point. Lucretius' **clinamen** — the swerve, the
minimal unmotivated deviation by which atoms falling through the void first depart from the
straight line and so can collide, combine, world. Duchamp's **inframince** (infrathin) — the
interval with no measurable extent that nonetheless separates two states (the warmth of a seat
just left, the difference between two castings from one mould). Both are the *first difference*.

`NullIsTheZero` fixed the void precisely: the null is the no-effect element — the still point
(the reflection's unique fixed point), the unique non-successor, the idempotent, the additive
unit. Against that, the clinamen states itself exactly:

> the clinamen is `succ 0` — the first successor of the null,

and the infrathin is its character: it is the **cover** of zero (`0 ⋖ 1`), an adjacency with no
interior; there is no smaller swerve. And the covering relation on `Nat` *is* the successor —
so every infrathin step is a clinamen, and (`NullIsTheZero` §-style, `…Coincidence` §9 as
cosmogony) every number is iterated clinamen: the world is the swerve, repeated, falling back
toward the void it left.

Builds on `Gnosis.NullIsTheZero`. Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace ClinamenInfrathin

open Gnosis.NullIsTheZero (Sign reflect)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The clinamen: the first successor of the null
-- ═══════════════════════════════════════════════════════════════════════

/-- The clinamen: the first successor of the null. The minimal swerve, `succ 0`. -/
def clinamen : Nat := 0 + 1

theorem clinamen_eq_one : clinamen = 1 := rfl

/-- The swerve breaks stillness: the clinamen is not the null. -/
theorem clinamen_ne_null : clinamen ≠ 0 := by decide

/-- The clinamen is a successor — it lies in the image of `+1`, unlike the null, which is the
    unique non-successor (`NullIsTheZero.zero_is_no_successor`). -/
theorem clinamen_is_a_successor : ∃ n, clinamen = n + 1 := ⟨0, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The infrathin: an adjacency with no interior
-- ═══════════════════════════════════════════════════════════════════════

/-- `b` covers `a` — the infrathin/adjacency relation: `a < b` with nothing strictly between.
    Duchamp's inframince, the threshold that has no inside. -/
def Covers (a b : Nat) : Prop := a < b ∧ ∀ c, a < c → ¬ (c < b)

/-- **Every infrathin step is a clinamen.** The covering relation on `Nat` is exactly the
    successor: an adjacency with no interior is a single `+1`. The swerve has no parts. -/
theorem covers_iff_succ (a b : Nat) : Covers a b ↔ b = a + 1 := by
  constructor
  · rintro ⟨hab, hgap⟩
    rcases Nat.lt_or_ge (a + 1) b with h | h
    · exact absurd h (hgap (a + 1) (Nat.lt_succ_self a))
    · exact Nat.le_antisymm h hab
  · rintro rfl
    refine ⟨Nat.lt_succ_self a, ?_⟩
    intro c hac hcb
    exact absurd hac (Nat.not_lt.mpr (Nat.lt_succ_iff.mp hcb))

/-- The clinamen is the cover of the null: `0 ⋖ 1`. *The infrathin moment of the first `+1`.* -/
theorem clinamen_covers_null : Covers 0 clinamen :=
  (covers_iff_succ 0 clinamen).mpr rfl

/-- Indivisible: no swerve is smaller. Nothing lies strictly between the null and the clinamen
    — the gap clause of the cover, read as Lucretius' "least thing". -/
theorem infrathin_indivisible : ¬ ∃ k, 0 < k ∧ k < clinamen := by
  rintro ⟨k, hpos, hlt⟩
  exact clinamen_covers_null.2 k hpos hlt

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The swerve breaks the null's stillness
-- ═══════════════════════════════════════════════════════════════════════

/-- The clinamen breaks idempotence: `1 + 1 ≠ 1`. The null compounded with itself stays null
    (`NullIsTheZero.zero_is_the_unique_idempotent`); the clinamen, compounded, grows. -/
theorem clinamen_breaks_idempotence : clinamen + clinamen ≠ clinamen := by decide

/-- The swerve picks a direction. In sign-space the null is the reflection's still point; the
    clinamen is `+`, which the reflection moves. The clinamen *is* the breaking of the
    `+/−` symmetry the null held — the first choice of a way to fall. -/
theorem clinamen_swerves_from_the_still_point :
    reflect Sign.zero = Sign.zero ∧ reflect Sign.pos ≠ Sign.pos :=
  ⟨rfl, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §4  The unfolding: everything is iterated clinamen
-- ═══════════════════════════════════════════════════════════════════════

/-- One swerve. -/
def swerve (n : Nat) : Nat := n + 1

/-- Iterate the swerve `k` times. -/
def iterSwerve : Nat → Nat → Nat
  | 0,     x => x
  | k + 1, x => swerve (iterSwerve k x)

/-- **Everything is iterated clinamen.** Every number is `n` swerves from the null — the world
    is the clinamen, repeated. This is `Nat` as the initial `(1+−)`-algebra
    (`…Coincidence` §9) read as cosmogony: fold from the void by the swerve. -/
theorem all_is_iterated_clinamen (n : Nat) : iterSwerve n 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show swerve (iterSwerve k 0) = k + 1
      rw [ih]
      rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The statement
-- ═══════════════════════════════════════════════════════════════════════

/--
**The clinamen is the infrathin moment of the first `+1`.** Given the null fixed as the
no-effect element (`NullIsTheZero`):

1. `clinamen = 0 + 1` — the first successor of the null;
2. `clinamen_covers_null` — it is the cover of zero, `0 ⋖ 1`, the infrathin threshold;
3. `covers_iff_succ` — every infrathin step *is* a clinamen (the cover relation is the successor);
4. `infrathin_indivisible` — there is no smaller swerve;
5. `all_is_iterated_clinamen` — every number is iterated clinamen, the world fold from the void.

The swerve and the inframince were the same event all along: the minimal, indivisible departure
of the null from its own stillness — the first `+1`.
-/
theorem clinamen_is_the_first_successor :
    clinamen = 0 + 1 ∧
    Covers 0 clinamen ∧
    (∀ a b : Nat, Covers a b ↔ b = a + 1) ∧
    (¬ ∃ k, 0 < k ∧ k < clinamen) ∧
    (∀ n, iterSwerve n 0 = n) :=
  ⟨rfl, clinamen_covers_null, covers_iff_succ, infrathin_indivisible, all_is_iterated_clinamen⟩

end ClinamenInfrathin
end Gnosis
