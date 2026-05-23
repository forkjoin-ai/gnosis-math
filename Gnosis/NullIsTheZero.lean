import Init

/-!
# NullIsTheZero — the no-effect element, four ways

Across the contrarian / scheduler / interference work one point kept reappearing under different
names: the verdict `eq` (indistinguishability, the `StallIsOptimal` stall), the sign `0`, null
interference, the conservative fixed point `iter f T x = x` (zero net change over a period), and
the additive identity `+0`. They are not five facts; they are one point seen from five angles —
the element that *changes nothing*.

This module states that at its own level rather than as a corollary of a cardinality
investigation (where it first surfaced, `FiveVerdictOperatorCoincidence` §8–§9). The honest
status: this is the **unit law**, long owned by mathematics — the identity of a structure is
*defined* as the no-op. What is worth writing down cleanly is that the no-op is forced to be a
single point by four independent characterizations, each a one-line kernel check:

* **Algebraic.** In any monoid the identity is the unique left-acting no-op (`identity_unique`).
* **Idempotent.** The only thing that compounds with itself to itself is the nothing —
  `n + n = n → n = 0` (`zero_is_the_unique_idempotent`); generally, the unique idempotent of a
  cancellative monoid.
* **Symmetric.** On the sign trichotomy the zero is the unique fixed point of the reflection —
  the still point the `+/−` swap cannot move (`zero_is_the_unique_still_point`).
* **Successor.** The null is the absence of a step: equality is separation by `+0`, and `0` is
  the unique non-successor (`null_is_zero_steps`, `zero_is_no_successor`).

The forced coincidence of the *domain* middles (verdict `eq` ↔ sign `0` ↔ interference `null`)
is proven in `FiveVerdictOperatorCoincidence` §7; this module supplies the general reason those
collapses are not accidents — they are instances of the no-op.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace NullIsTheZero

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Algebraic: the identity is the unique no-op (the unit law)
-- ═══════════════════════════════════════════════════════════════════════

/-- A monoid: an associative operation with a two-sided identity. -/
structure Monoid (M : Type) where
  op : M → M → M
  e : M
  e_left  : ∀ x, op e x = x
  e_right : ∀ x, op x e = x
  assoc   : ∀ a b c, op (op a b) c = op a (op b c)

/-- **The unit law's content.** Any element that acts as a left identity already *is* the
    identity. The no-op is unique: `u = u ∘ e = e`. -/
theorem identity_unique {M : Type} (G : Monoid M) (u : M)
    (hu : ∀ x, G.op u x = x) : u = G.e :=
  (G.e_right u).symm.trans (hu G.e)

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Idempotent: the only self-compounding no-op is nothing
-- ═══════════════════════════════════════════════════════════════════════

/-- The additive monoid on `Nat`. -/
def natAdd : Monoid Nat where
  op := Nat.add
  e := 0
  e_left := Nat.zero_add
  e_right := Nat.add_zero
  assoc := Nat.add_assoc

/-- The additive no-op on `Nat` is unique and is `0` (the unit law, instantiated). -/
theorem zero_is_the_additive_noop (u : Nat) (hu : ∀ x, u + x = x) : u = 0 :=
  identity_unique natAdd u hu

/-- **The unique idempotent.** The only thing that, combined with itself, yields itself is the
    nothing: `n + n = n → n = 0`. (Holds in any cancellative monoid; here on `Nat`. Proven via
    the order rather than cancellation, to stay axiom-free: a positive `n` is strictly below
    `n + n`, so it cannot equal it.) -/
theorem zero_is_the_unique_idempotent (n : Nat) (h : n + n = n) : n = 0 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact h0
  · exact absurd h.symm (Nat.ne_of_lt (Nat.lt_add_of_pos_right hpos))

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Symmetric: zero is the still point of the reflection
-- ═══════════════════════════════════════════════════════════════════════

/-- The sign trichotomy `{-, 0, +}`. -/
inductive Sign | neg | zero | pos
  deriving DecidableEq, Repr

/-- The reflection (negation): the involution that swaps `±` and fixes `0`. -/
def reflect : Sign → Sign | .neg => .pos | .zero => .zero | .pos => .neg

theorem reflect_involutive (s : Sign) : reflect (reflect s) = s := by cases s <;> rfl

/-- **The still point.** Zero is the unique fixed point of the reflection — the one place the
    `+/−` symmetry has nothing left to move. -/
theorem zero_is_the_unique_still_point : ∀ s : Sign, reflect s = s → s = .zero := by
  intro s
  cases s
  · intro h; exact absurd h (by decide)
  · intro _; rfl
  · intro h; exact absurd h (by decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Successor: the null is the absence of a step
-- ═══════════════════════════════════════════════════════════════════════

/-- Zero is the unique non-successor: nothing steps onto it. -/
theorem zero_is_no_successor (n : Nat) : 0 ≠ n + 1 := fun h => Nat.succ_ne_zero n h.symm

/-- Null is zero successor steps: equality is separation by `+0`. -/
theorem null_is_zero_steps (a b : Nat) : a = b ↔ b = a + 0 := by
  rw [Nat.add_zero]; exact ⟨Eq.symm, Eq.symm⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The statement
-- ═══════════════════════════════════════════════════════════════════════

/--
**Null is the zero.** The no-effect element is a single point, characterized four independent
ways — algebraic identity, unique idempotent, reflection's still point, and the absence of a
successor step:

1. `identity_unique` — in any monoid, a left-acting no-op is the identity;
2. `zero_is_the_unique_idempotent` — the only self-compounding no-op is nothing;
3. `zero_is_the_unique_still_point` — zero is the reflection's unique fixed point;
4. `null_is_zero_steps` — equality is separation by `+0`.

The domain readings — verdict `eq`, interference `null`, the conservative fixed point — are
instances; their forced coincidence is `FiveVerdictOperatorCoincidence` §7. This is the unit
law, stated at the level it deserves.
-/
theorem null_is_the_zero :
    (∀ (M : Type) (G : Monoid M) (u : M), (∀ x, G.op u x = x) → u = G.e) ∧
    (∀ n : Nat, n + n = n → n = 0) ∧
    (∀ s : Sign, reflect s = s → s = .zero) ∧
    (∀ a b : Nat, a = b ↔ b = a + 0) :=
  ⟨fun _ G u hu => identity_unique G u hu,
   zero_is_the_unique_idempotent,
   zero_is_the_unique_still_point,
   null_is_zero_steps⟩

end NullIsTheZero
end Gnosis
