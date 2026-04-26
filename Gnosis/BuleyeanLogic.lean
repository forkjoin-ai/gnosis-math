import Init

namespace Gnosis

/-!
# Buleyean Logic

A post-fold logic where truth is ground state and proof is rejection.

Boolean logic describes the world after the fold: {true, false}.
Buleyean logic describes the world during convergence: natural numbers
decreasing toward zero as rejections accumulate.

## Primitives

- A proposition is a natural number (the Bule count)
- 0 = proved (ground state)
- n > 0 = n rejections remain
- The only proof step is rejection (decrement by 1)

## Connectives

- NOT A = maxBules - A
- A AND B = A + B
- A OR B = min(A, B)
- A → B = max(0, B - A)
- FORALL = sum
- EXISTS = min

## Self-hosting

This file proves the laws of Buleyean logic using Lean 4, then
proves that Boolean logic is the K=2 special case, establishing
that Buleyean subsumes Boolean.

The next step (Gnosis) will prove these laws using Buleyean logic
itself.  This Lean proof is the bootstrap.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════════════════════════════════

/-- A Buleyean proposition is a natural number: the Bule count. -/
abbrev BProp := Nat

/-- Ground state: proved. -/
def bProved : BProp := 0

/-- Open: n Bules of deficit remain. -/
def bOpen (n : Nat) : BProp := n

/-- Is a proposition proved? -/
def bIsProved (p : BProp) : Prop := p = 0

-- ═══════════════════════════════════════════════════════════════════════
-- The only proof step: rejection
-- ═══════════════════════════════════════════════════════════════════════

/-- Rejection: decrease the Bule count by 1. -/
def bReject (p : BProp) : BProp := p - 1

/-- Rejection at ground state is a no-op. -/
theorem reject_at_ground : bReject 0 = 0 := rfl

/-- Rejection decreases the Bule count by 1 when positive. -/
theorem reject_decreases (p : BProp) (_hp : 0 < p) :
    bReject p = p - 1 := rfl

/-- Helper for n iterations. -/
def nIterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (nIterate f n x)

/-- n rejections from start reach ground state in n steps if start <= n. -/
theorem nIterate_bReject_eq (m n : Nat) : nIterate bReject m n = n - m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    conv =>
      lhs
      unfold nIterate
    rw [ih]
    exact Nat.sub_sub n k 1

/-- n rejections from n reach ground state. -/
theorem n_rejections_reach_ground (n : Nat) :
    nIterate bReject n n = 0 := by
  rw [nIterate_bReject_eq]
  exact Nat.sub_self n

-- ═══════════════════════════════════════════════════════════════════════
-- Connectives
-- ═══════════════════════════════════════════════════════════════════════

/-- AND: both must reach ground. Cost = sum. -/
def bAnd (a b : BProp) : BProp := a + b

/-- OR: at least one must reach ground. Cost = minimum. -/
def bOr (a b : BProp) : BProp := Nat.min a b

/-- NOT: the complement. -/
def bNot (a : BProp) (maxB : Nat) : BProp := maxB - a

/-- IMPLIES: A → B holds when resolving A subsumes resolving B. -/
def bImplies (a b : BProp) : BProp := b - a

-- ═══════════════════════════════════════════════════════════════════════
-- Laws of Buleyean Logic
-- ═══════════════════════════════════════════════════════════════════════

-- --- AND ---

/-- AND is commutative. -/
theorem bAnd_comm (a b : BProp) : bAnd a b = bAnd b a := Nat.add_comm a b

/-- AND is associative. -/
theorem bAnd_assoc (a b c : BProp) : bAnd (bAnd a b) c = bAnd a (bAnd b c) := Nat.add_assoc a b c

/-- AND with proved is identity. -/
theorem bAnd_proved (a : BProp) : bAnd a 0 = a := Nat.add_zero a

/-- AND is proved iff both are proved. -/
theorem bAnd_proved_iff (a b : BProp) : bIsProved (bAnd a b) ↔ bIsProved a ∧ bIsProved b := by
  unfold bIsProved bAnd
  exact Nat.add_eq_zero_iff

-- --- OR ---

/-- OR is commutative. -/
theorem bOr_comm (a b : BProp) : bOr a b = bOr b a := Nat.min_comm a b

/-- OR is associative. -/
theorem bOr_assoc (a b c : BProp) : bOr (bOr a b) c = bOr a (bOr b c) := Nat.min_assoc a b c

/-- OR with proved is proved. -/
theorem bOr_proved (a : BProp) : bOr a 0 = 0 := Nat.min_zero a

/-- OR is proved iff at least one is proved. -/
theorem bOr_proved_iff (a b : BProp) : bIsProved (bOr a b) ↔ bIsProved a ∨ bIsProved b := by
  unfold bIsProved bOr
  exact Nat.min_eq_zero_iff

-- --- NOT ---

/-- Double complement: NOT NOT A = A (when A ≤ maxB). -/
theorem bNot_bNot (a : BProp) (maxB : Nat) (h : a ≤ maxB) :
    bNot (bNot a maxB) maxB = a := by
  unfold bNot
  exact Nat.sub_sub_self h

/-- NOT of proved = maximally open. -/
theorem bNot_proved (maxB : Nat) : bNot 0 maxB = maxB := Nat.sub_zero maxB

/-- NOT of maximally open = proved. -/
theorem bNot_open (maxB : Nat) : bNot maxB maxB = 0 := Nat.sub_self maxB

-- --- IMPLIES ---

/-- A → A is always proved (zero deficit). -/
theorem bImplies_refl (a : BProp) : bImplies a a = 0 := Nat.sub_self a

/-- If A is harder than B, A → B is proved. -/
theorem bImplies_of_ge (a b : BProp) (h : b ≤ a) : bImplies a b = 0 := Nat.sub_eq_zero_of_le h

-- --- OR is cheaper than AND ---

/-- OR ≤ AND always. Disjunction costs less than conjunction. -/
theorem bOr_le_bAnd (a b : BProp) : bOr a b ≤ bAnd a b := by
  unfold bOr bAnd
  exact Nat.le_trans (Nat.min_le_left a b) (Nat.le_add_right a b)

-- ═══════════════════════════════════════════════════════════════════════
-- Boolean Embedding: Buleyean subsumes Boolean
-- ═══════════════════════════════════════════════════════════════════════

/-- Boolean true → 0 Bules.  Boolean false → 1 Bule. -/
def bFromBool (b : Bool) : BProp := if b then 0 else 1

/-- Buleyean proposition → Boolean (proved = true). -/
def bToBool (p : BProp) : Bool := p == 0

/-- Round-trip: Bool → BProp → Bool. -/
theorem bool_roundtrip (b : Bool) : bToBool (bFromBool b) = b := by
  cases b <;> rfl

/-- AND matches Boolean AND at K=2. -/
theorem bAnd_matches_bool (a b : Bool) :
    bToBool (bAnd (bFromBool a) (bFromBool b)) = (a && b) := by
  cases a <;> cases b <;> rfl

/-- OR matches Boolean OR at K=2. -/
theorem bOr_matches_bool (a b : Bool) :
    bToBool (bOr (bFromBool a) (bFromBool b)) = (a || b) := by
  cases a <;> cases b <;> rfl

/-- NOT matches Boolean NOT at K=2. -/
theorem bNot_matches_bool (a : Bool) :
    bToBool (bNot (bFromBool a) 1) = !a := by
  cases a <;> rfl

-- ═══════════════════════════════════════════════════════════════════════
-- Master theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-BULEYEAN-LOGIC**: The laws hold and Boolean is a special case.

    1. Rejection reaches ground state in n steps
    2. AND is commutative, associative, proved iff both proved
    3. OR is commutative, associative, proved iff at least one proved
    4. NOT is involutive, maps proved ↔ maximally open
    5. IMPLIES is reflexive, trivial when premise is harder
    6. OR ≤ AND (disjunction is cheaper)
    7. Boolean AND/OR/NOT are recovered at K=2 -/
theorem buleyean_logic :
    -- (1) n rejections from n → ground
    (∀ n : Nat, nIterate bReject n n = 0) ∧
    -- (2) AND laws
    (∀ a b : BProp, bAnd a b = bAnd b a) ∧
    (∀ a b : BProp, bIsProved (bAnd a b) ↔ bIsProved a ∧ bIsProved b) ∧
    -- (3) OR laws
    (∀ a b : BProp, bOr a b = bOr b a) ∧
    (∀ a b : BProp, bIsProved (bOr a b) ↔ bIsProved a ∨ bIsProved b) ∧
    -- (4) NOT involution
    (∀ maxB : Nat, bNot 0 maxB = maxB) ∧
    (∀ maxB : Nat, bNot maxB maxB = 0) ∧
    -- (5) IMPLIES reflexivity
    (∀ a : BProp, bImplies a a = 0) ∧
    -- (6) OR ≤ AND
    (∀ a b : BProp, bOr a b ≤ bAnd a b) ∧
    -- (7) Boolean embedding
    (∀ b : Bool, bToBool (bFromBool b) = b) ∧
    (∀ a b : Bool, bToBool (bAnd (bFromBool a) (bFromBool b)) = (a && b)) ∧
    (∀ a b : Bool, bToBool (bOr (bFromBool a) (bFromBool b)) = (a || b)) := by
  exact ⟨
    n_rejections_reach_ground,
    bAnd_comm, bAnd_proved_iff,
    bOr_comm, bOr_proved_iff,
    bNot_proved, bNot_open,
    bImplies_refl,
    bOr_le_bAnd,
    bool_roundtrip, bAnd_matches_bool, bOr_matches_bool
  ⟩

end Gnosis
