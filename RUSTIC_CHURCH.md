# Rustic Church: Init-only proofs for gnosis-math

## What this is

The **Rustic Church** style proves theorems in `gnosis-math` using *only*
definitional unfolding plus structurally inductive Init-level `Nat.*` lemmas.
No `omega`, no `simp`, no `decide` for open-variable goals, no Mathlib.

Every Init lemma cited below is provable from `Nat.succ` (the `+1` clinamen)
by structural induction. The kernel is therefore self-bootstrapping: if `lake
build` accepts a Rustic Church module, the formula's algebra has been
re-derived from the inductive `+1` alone, and internal consistency follows.

The canonical exemplar is [`Gnosis/GodFormula.lean`](Gnosis/GodFormula.lean):
nine theorems (conservation, ceiling, floor, positivity, sandwich,
antitonicity, and three internal-consistency cross-checks), zero `omega` /
`simp` / `decide`.

## When to drop omega vs. when to keep it

**Drop `omega` when** the goal, after `unfold`, fits one of the patterns in
the cookbook below. These are 90% of `omega` calls in practice:

- Successor-shaped: `0 < n + 1`, `n < n + 1`, `n ≤ n + 1`.
- Saturating sub identities: `(n - 1) + 1 = n` (with `0 < n`), `(n + 1) - 1 = n`.
- Add commutativity / associativity / right-comm.
- Monotonicity through one operator (sub-left, add-right, mul-right).
- Closed numeric goals (no free vars after unfolds): `decide`.
- Impossible match branches: `absurd h (by decide)`.

**Keep `omega` (for now) when** the proof simultaneously juggles 3+ Nat-sub
facts, mixes Int and Nat across a cast boundary, or chains modular arithmetic
through several rewrites. Those are tractable but expensive to spell out
inductively; a `TODO(rustic-church)` comment is fine.

`decide` is acceptable for *closed* numeric goals (no free vars) — it's still
kernel-checked, just slower than a named lemma. `native_decide` is acceptable
for large finite checks (it trusts the compiler too, but the trade is huge
search spaces).

## Cookbook

### Successor / `+1` (clinamen) shapes

```lean
example (n : Nat) : 0 < n + 1 := Nat.succ_pos n
example (n : Nat) : n < n + 1 := Nat.lt_succ_self n
example (n : Nat) : n ≤ n + 1 := Nat.le_succ n
example {n m : Nat} (h : n ≤ m) : n + 1 ≤ m + 1 := Nat.succ_le_succ h
example (n : Nat) : 0 ≤ n := Nat.zero_le n
```

`0 < n` and `1 ≤ n` are *definitionally equal* in Lean 4 — pass `hK : 1 ≤ K`
where `0 < K` is expected, no conversion needed.

### Saturating subtraction `a - b`

This is where omega earns most of its keep, but Init has clean lemmas:

```lean
-- (n - 1) + 1 = n, given 0 < n
example {n : Nat} (h : 0 < n) : (n - 1) + 1 = n := Nat.sub_add_cancel h

-- (n + 1) - 1 = n  (no hypothesis needed; pure structural)
example (n : Nat) : (n + 1) - 1 = n := Nat.add_sub_cancel

-- (a + b) - a = b
example (a b : Nat) : a + b - a = b := Nat.add_sub_cancel_left a b
-- ⚠ In Lean 4.28 this lemma takes BOTH args explicitly. If you write
--   `exact Nat.add_sub_cancel_left` Lean asks for the args.

-- a - b ≤ a
example (a b : Nat) : a - b ≤ a := Nat.sub_le a b

-- monotone: more rejected ⇒ less weight (antitone in subtrahend)
example {n m : Nat} (h : n ≤ m) (k : Nat) : k - m ≤ k - n :=
  Nat.sub_le_sub_left h k

-- "k ≤ a, a < k + n ⇒ a - k < n"
example {k a n : Nat} (h₁ : k ≤ a) (h₂ : a < k + n) : a - k < n :=
  Nat.sub_lt_left_of_lt_add h₁ h₂

-- inverse phrasings
example {k m n : Nat} (h : k + m ≤ n) : m ≤ n - k :=
  Nat.le_sub_of_add_le h
example {k m n : Nat} (h : k + m < n) : m < n - k :=
  Nat.lt_sub_of_add_lt h

-- m + (n - m) = n  (commuted Nat.sub_add_cancel)
example {m n : Nat} (h : m ≤ n) : m + (n - m) = n := Nat.add_sub_of_le h

-- saturation collapses at boundaries
example {a b : Nat} (h : a ≤ b) : a - b = 0 := Nat.sub_eq_zero_of_le h
example {a b : Nat} (h : a - b = 0) : a ≤ b := Nat.le_of_sub_eq_zero h
example {a b : Nat} (h : a < b) : 0 < b - a := Nat.sub_pos_of_lt h
example (n : Nat) : n - n = 0 := Nat.sub_self n
example (n : Nat) : n - 0 = n := Nat.sub_zero n
```

### Addition manipulation

```lean
example (a b c : Nat) : a + b + c = a + c + b := Nat.add_right_comm a b c
example (a b : Nat) : a + b = b + a := Nat.add_comm a b
example (a b c : Nat) : a + b + c = a + (b + c) := Nat.add_assoc a b c

example (a b : Nat) : a ≤ a + b := Nat.le_add_right a b
example (a b : Nat) : a ≤ b + a := Nat.le_add_left a b
example {a b : Nat} (h : 0 < b) : a < a + b := Nat.lt_add_of_pos_right h
example {a b : Nat} (h : 0 < a) : b < a + b := Nat.lt_add_of_pos_left h

example {a b : Nat} (h : a ≤ b) (k : Nat) : a + k ≤ b + k :=
  Nat.add_le_add_right h k
example {a b : Nat} (h : a < b) (k : Nat) : a + k < b + k :=
  Nat.add_lt_add_right h k
```

`Nat.add` reduces by recursion on the **right** argument, so:

```lean
example (a b : Nat) : a + (b + 1) = a + b + 1 := rfl   -- definitional!
```

Use this constantly: `n + (k + 1)` is `(n + k) + 1` for free.

### Multiplication

```lean
example (m k : Nat) (h : 0 < k) : m ≤ k * m := Nat.le_mul_of_pos_left m h
example (a b : Nat) (v : Nat) (h : a ≤ b) : a * v ≤ b * v :=
  Nat.mul_le_mul_right v h

example (n : Nat) : 2 * n = n + n := Nat.two_mul n
example (n m : Nat) : n * (m + 1) = n * m + n := Nat.mul_succ n m
example (n m : Nat) : (n + 1) * m = n * m + m := Nat.succ_mul n m
```

### Division

```lean
example (n k : Nat) : n / k ≤ n := Nat.div_le_self n k
-- 0 < k ≤ n ⇒ 0 < n / k
example {k n : Nat} (h₁ : k ≤ n) (h₂ : 0 < k) : 0 < n / k :=
  Nat.div_pos h₁ h₂
-- antitone in divisor: dividing by more gives less
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : 0 < a) : c / b ≤ c / a :=
  Nat.div_le_div_left h₁ h₂
```

### Order, transitivity, antisymmetry

```lean
example (n : Nat) : n ≤ n := Nat.le_refl n
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := Nat.le_trans h₁ h₂
example {a b c : Nat} (h₁ : a < b) (h₂ : b ≤ c) : a < c := Nat.lt_of_lt_of_le h₁ h₂
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := Nat.lt_of_le_of_lt h₁ h₂
example {a b : Nat} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := Nat.le_antisymm h₁ h₂
example {a b : Nat} (h₁ : a < b) : a ≤ b := Nat.le_of_lt h₁
example {a b : Nat} (h : ¬ b < a) : a ≤ b := Nat.le_of_not_gt h
example {a b : Nat} (h : a ≤ b) : ¬ b < a := Nat.not_lt_of_le h
```

### Discharging impossible cases

When `match` / `cases` produces a branch whose hypothesis is contradictory:

```lean
-- hn : 1 ≤ 0 — impossible
example (hn : 1 ≤ 0) : False := absurd hn (by decide)

-- hn : 2 ≤ n + 1, but match branch already pinned n + 1 = 1
example (hn : 2 ≤ 1) : False := absurd hn (by decide)

-- n + 22 ≤ 21 for any Nat n — impossible because 21 < 22 ≤ n + 22
example (n : Nat) (h21 : n + 22 ≤ 21) : False :=
  Nat.not_le_of_lt
    (Nat.lt_of_lt_of_le (by decide : (21 : Nat) < 22) (Nat.le_add_left 22 n))
    h21

-- universal: n < 0 is impossible for Nat
example (n : Nat) (h : n < 0) : False := Nat.not_lt_zero n h
```

### Nat → Int casts

`((n + 1 : Nat) : Int) = (n : Int) + 1` reduces by `rfl`. Past that, lean on:

```lean
example (a : Int) (b : Nat) : a - ((b + 1 : Nat) : Int) = a - (b : Int) - 1 := by
  show a - ((b : Int) + 1) = a - (b : Int) - 1
  rw [show (a - (b : Int) - 1) = a + (-(b : Int) + (-1)) from by
        rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_assoc, ← Int.neg_add]]
  rw [Int.sub_eq_add_neg, Int.neg_add]
```

Genuine Int-linear chains are still in the "keep omega for now" zone — see
the `meta_truth_constancy` proof in `Gnosis/TopologicalMetabolism.lean` for
the working pattern.

### Bool / Prop coercion (the Prop→Bool refactor)

If you switch a definition's return type from `Prop` to `Bool` and the body
mixes `Bool && Prop`, Lean coerces the Prop side via `decide`. To unpack
`f x = true` where `f` returns Bool:

```lean
-- decide_eq_true_iff and decide_eq_false_iff take NO explicit args in 4.28
example (p : Prop) [Decidable p] (h : decide p = true) : p :=
  decide_eq_true_iff.mp h
-- Functional shortcuts (preferred for term-mode):
example (p : Prop) [Decidable p] (h : decide p = true) : p := of_decide_eq_true h
example (p : Prop) [Decidable p] (h : ¬ p) : decide p = false := decide_eq_false h
example (p : Prop) [Decidable p] (h : decide p = false) : ¬ p := of_decide_eq_false h

-- Bool && Bool unpack:
example (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true :=
  (Bool.and_eq_true a b).mp h
```

Pattern for nested `Bool` defs (e.g. `truthState p m d := truthExists p m ∧ isCoherent d`,
both Bool, so the body's `∧` is on Props with the Bools coerced via `= true`,
then the whole thing is `decide`'d to Bool):

```lean
intro hTruth                                              -- hTruth : truthState p m d = true
have hPair : truthExists p m = true ∧ isCoherent d = true :=
  of_decide_eq_true hTruth                                -- peel one decide layer
exact use_of_pair hPair.1 hPair.2
```

If a `def f : Bool := P` won't elaborate because `P : Prop` needs an
explicit `decide`, write `def f : Bool := decide P`. Lean does not auto-coerce
Prop → Bool inside `def` bodies even though it does so inside expressions.

### `repeat constructor` does not descend

In Lean 4.28, `repeat tac` only repeats on the current main goal until `tac`
fails, then stops. For an N-ary `∧` chain `A ∧ B ∧ C ∧ ... ∧ Z`, the first
`constructor` produces goals `A` and `B ∧ C ∧ ... ∧ Z`; `constructor` fails
on `A` so `repeat` stops with two goals open, not N.

For master-bundle theorems, prefer:

```lean
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· exact ...
· exact ...
...
```

with one placeholder per top-level conjunct.

## Worked migration patterns

These are the substitutions that came up repeatedly while sweeping
omega-heavy files. If you see the LHS, the RHS usually works.

| Goal shape | Replacement |
|---|---|
| `0 < n + 1` | `Nat.succ_pos _` |
| `n < n + 1` | `Nat.lt_succ_self _` |
| `n ≤ n + 1` | `Nat.le_succ _` |
| `n ≤ n + k` | `Nat.le_add_right _ _` |
| `n < n + k` (with `0 < k`) | `Nat.lt_add_of_pos_right h` |
| `(n - 1) + 1 = n` (with `0 < n`) | `Nat.sub_add_cancel h` |
| `(n + 1) - 1 = n` | `Nat.add_sub_cancel` |
| `a + b - a = b` | `Nat.add_sub_cancel_left a b` |
| `m + (n - m) = n` (with `m ≤ n`) | `Nat.add_sub_of_le h` |
| `n - m ≤ n` | `Nat.sub_le n m` |
| `k - m ≤ k - n` (with `n ≤ m`) | `Nat.sub_le_sub_left h k` |
| `0 < n - m` (with `m < n`) | `Nat.sub_pos_of_lt h` |
| `1 ≤ K - 1` (with `2 ≤ K`) | `Nat.le_sub_of_add_le h` |
| `1 < K - 1` (with `3 ≤ K`) | `Nat.lt_sub_of_add_lt (Nat.lt_of_lt_of_le (by decide) h)` |
| `a + b + c = a + c + b` | `Nat.add_right_comm a b c` |
| `a + 0 = a` | `Nat.add_zero a` |
| `a = b` from `a ≤ b` and `b ≤ a` | `Nat.le_antisymm h₁ h₂` |
| `a < c` from `a < b` and `b ≤ c` | `Nat.lt_of_lt_of_le h₁ h₂` |
| `n ≤ k * n` (with `0 < k`) | `Nat.le_mul_of_pos_left n h` |
| `a * v ≤ b * v` (with `a ≤ b`) | `Nat.mul_le_mul_right v h` |
| `n * (m + 1) = n * m + n` | `Nat.mul_succ n m` |
| `2 * n = n + n` | `Nat.two_mul n` |
| `False` from impossible Nat literal | `absurd h (by decide)` |
| Closed numeric (no free vars) | `decide` |
| Closed numeric, big search space | `native_decide` |

## How to migrate a file (workflow)

1. Inventory: `grep -nE "\bomega\b" Gnosis/Foo.lean`.
2. Take a backup: `cp Gnosis/Foo.lean /tmp/foo_backup.lean`.
3. Bulk attempt: `sed -i '' -e 's|; omega$|; decide|g' -e 's|^  omega$|  decide|g' -e 's|by omega$|by decide|g' Gnosis/Foo.lean`.
4. Build: `lake build Gnosis.Foo 2>&1 | grep "^error" | sed -E 's|.*lean:([0-9]+):.*|\1|' | sort -un`.
5. Each line that errored has a free variable — revert it: `sed -i '' "${L}s|decide|omega|" Gnosis/Foo.lean` and convert by hand using the cookbook above.
6. The lines that didn't error are now `decide`-closed. Move on.
7. Re-build until green, run full `lake build` to make sure no downstream consumer broke.

Most files split roughly 70/30: closed numerics (bulk → `decide`) vs.
free-variable goals (hand-translate using the cookbook). The hand-translate
work usually compresses 3-5 omegas per Init lemma name once you spot the
shape.

## Cracking 3+ saturating-sub proofs

*This used to be in "what still needs omega". After
[`Gnosis/HumanCompiler.lean`](Gnosis/HumanCompiler.lean),
[`Gnosis/SelfHostingOptimality.lean`](Gnosis/SelfHostingOptimality.lean),
and [`Gnosis/TenModeUnification.lean`](Gnosis/TenModeUnification.lean)
all landed Init-only, the recipe is known.*

The trick is naming each fact and chaining them — `omega` does this in one
opaque step, but the manual version reads cleaner once you do it.

### Pattern 1: Convergence by induction on cost ladder (`stable_from`)

The shape: `∀ v, cost s ≤ v → ∃ N, ...`. Induct on `v`. Two key sub-cases:

- **Strict drop, recurse one budget tighter.** From `cost (s+1) < cost s`
  and `cost s ≤ v + 1`, derive `cost (s+1) ≤ v` by
  `Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdrop hle)`.
  Then bump the existential's `N` upper bound from `s+1 ≤ N` to `s ≤ N` via
  `Nat.le_trans (Nat.le_succ s) hN1`.
- **Plateau (no drop, no slack).** From `¬(cost (s+1) < cost s)` get
  `cost s ≤ cost (s+1)` via `Nat.le_of_not_lt`, then `cost (s+1) = cost s`
  via `Nat.le_antisymm (h s) hSleStep`. From `¬(cost (s+1) ≤ v)` get
  `v + 1 ≤ cost (s+1)` via `Nat.succ_le_of_lt (Nat.lt_of_not_le hle2)`.
  Bridge through the equality and you have `cost s = v + 1`.

The pattern that closes the inner "every later step also equals v+1" lemma:
`Nat.le_antisymm (hval ▸ monotone_descent ...) (Nat.le_of_not_lt hlt)`.

### Pattern 2: `n - r_j < n - r_i` via difference peeling

Given `r_i < r_j ≤ n`, prove `n - r_j < n - r_i`. Don't reach for sub
inequalities directly — peel `n - r_j = (n - r_i) - (r_j - r_i)` and apply
`Nat.sub_lt_self`:

```lean
have hLe : r_i ≤ r_j := Nat.le_of_lt h
have hDiffPos : 0 < r_j - r_i := Nat.sub_pos_of_lt h
have hDiffLeT : r_j - r_i ≤ n - r_i := Nat.sub_le_sub_right bj r_i
have hPeel : n - r_j = (n - r_i) - (r_j - r_i) := by
  rw [Nat.sub_sub, Nat.add_sub_of_le hLe]
rw [hPeel]
exact Nat.sub_lt_self hDiffPos hDiffLeT
```

### Pattern 3: Master-bundle by `Nat.lt_or_ge` + bound-style refute

When the goal is `f x = K ↔ x = K_value`, split on `x` against `K_value + 1`,
then split the lower side on `K_value`, and refute each off-band case with
`absurd h_after_rw (by decide)` — once you `rw [h]` into the bound, the
remaining inequality is a closed-numeric `66 ≤ 55` (or similar) that
`by decide` flatly contradicts.

Useful disjunction shaper:

```lean
-- worlds < N+1 → (worlds ≤ N-1 ∨ N ≤ worlds)
example (worlds N : Nat) (hLt : worlds < N + 1) : worlds ≤ N ∨ N ≤ worlds :=
  (Nat.lt_or_ge worlds N).imp Nat.le_of_lt_succ id
```

The "= 10" closer in the band is just `Nat.le_antisymm (Nat.le_of_lt_succ hLt) hGeTen`.

### Pattern 4: Modular arithmetic with bounded operands

Goal shape: `(a + N - b) % N = 0` with `a, b < N` ⇒ `a = b`. The divisibility
argument decomposes into "0 < (sum) < 2N, only multiple of N in that range
is N itself."

```lean
have hDvd : N ∣ (q + N - p) := Nat.dvd_of_mod_eq_zero hk_zero
have hpLeQN : p ≤ q + N := Nat.le_trans (Nat.le_of_lt hp) (Nat.le_add_left N q)
have hPos  : 0 < q + N - p := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le hp (Nat.le_add_left N q))
have hLt2N : q + N - p < 2 * N := by
  -- left as exercise; bound q + N < N + N = 2N, then sub_le.
  ...
obtain ⟨k, hkEq⟩ := hDvd
-- k must be 1: k = 0 ⇒ q + N - p = 0 (contradicts hPos);
-- k ≥ 2 ⇒ q + N - p ≥ 2N (contradicts hLt2N).
have hkOne : k = 1 := ...
rw [hkOne, Nat.mul_one] at hkEq
-- hkEq : q + N - p = N. Add p to both sides; cancel.
have : q + N = p + N := by
  have hAdd : (q + N - p) + p = N + p := by rw [hkEq]
  rw [Nat.sub_add_cancel hpLeQN] at hAdd
  rw [hAdd, Nat.add_comm N p]
exact (Nat.add_right_cancel this).symm
```

The supporting lemmas are `Nat.dvd_of_mod_eq_zero`, `Nat.sub_pos_of_lt`,
`Nat.add_right_cancel`. Worked example: `helix55_encode_decode` in
`Gnosis/Helix55Dictionary.lean`.

For the simpler `(i + N) % N = i` case (`i < N`), use
`Nat.add_mod_right` followed by `Nat.mod_eq_of_lt hi`.

### Pattern 5b: Reflexive omega — when the hypothesis IS the goal

Watch for `theorem foo (h : P) : P := by omega` — omega is being asked to
re-derive `P` from `P`, so the proof is just `h`. The `Gnosis/Dewey*ThinTopology.lean`
files held ~80 omegas of this shape; they all collapse to `:= h` term-mode.

Companion micro-patterns from the same files:

| Goal | Hypothesis | Replacement |
|---|---|---|
| `x = 0` | `h : x = nodes * 0` | `h.trans (Nat.mul_zero nodes)` |
| `x = y` | `h : x = y * 1` | `h.trans (Nat.mul_one y)` |
| `x ≥ y` | `h : x = y + z` | `h ▸ Nat.le_add_right y z` |
| `x ≤ y` | `h : x = y - z` | `h ▸ Nat.sub_le y z` |
| `n ≥ 0` | (anything) | `Nat.zero_le _` (drop the trivial hypothesis) |
| `parser + m ≥ parser` | `h : m ≥ 0` | `Nat.le_add_right parser m` (h is unused) |

If you see `theorem foo (h : trivial_for_Nat) : ...` and the proof is omega,
the hypothesis is probably noise. Mark it `_h` and use the structural lemma.

### Pattern 5: `iterateSucc`-style period lemmas

`iterateSucc n (m + 1) i = (i + 1 + m) % n` is provable by induction on
`m`. The recurring shape inside the proof is `(x % n + (1 + k)) % n =
(x + (1 + k)) % n`, which is `mod_add_left` (or `add_mod_right` for the
mirror). Both are one-line `rw` chains:

```lean
private theorem mod_add_left (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
```

### Pattern 5c: Polynomial expansion `(n+1)(b+1) = n*b + n + b + 1`

For a single-step factorization (helper lemmas like
`succ_succ_add_le_mul_succ` in `Gnosis/PipelineSpeedup.lean`):

```lean
have hexp : (n + 1) * (b + 1) = n * b + n + b + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
  simp [Nat.mul_one, Nat.one_mul]
  ac_rfl  -- handles the residual reordering
```

When the next step needs `(n+1)+(b+1) ≤ (n+1)*(b+1) + 1`, chain via
`calc` with `Nat.le_add_left` between two `ac_rfl` rearrangements:

```lean
calc (n + 1) + (b + 1)
    = n + b + 2 := by ac_rfl
  _ ≤ n * b + (n + b + 2) := Nat.le_add_left _ _
  _ = n * b + n + b + 1 + 1 := by
      rw [show (2 : Nat) = 1 + 1 from rfl]; ac_rfl
```

`ac_rfl` doesn't split numeric literals, so reify `2 = 1 + 1` (or
`3 = 1 + 1 + 1` etc.) before invoking it.

### Pattern 5d: Bounded division `(n * a) / b ≤ n` (with `a ≤ b`)

`(n * 3) / 4 ≤ n`, the `shrinkStep` shape from
`Gnosis/IteratedBizarroShrink.lean`:

```lean
calc (n * 3) / 4
    ≤ (n * 4) / 4 := Nat.div_le_div_right
        (Nat.mul_le_mul_left n (by decide : (3 : Nat) ≤ 4))
  _ = n := Nat.mul_div_cancel n (by decide : 0 < 4)
```

Generalisation: when you have a quotient bounded by a constant ratio,
inflate the dividend until the divisor cancels exactly, then collapse.

### Pattern 5e: Divisibility-strict `obtain ⟨k, rfl⟩` peeling

When you have `h : k ∣ n` and need to compute `n / k` exactly, peel `n`
to `k * j` and use `Nat.mul_div_cancel_left`:

```lean
unfold shrinkStep
obtain ⟨k, rfl⟩ := h  -- n becomes 4 * k
-- Goal: (4 * k * 3) / 4 * 4 = 4 * k * 3
rw [Nat.mul_assoc 4 k 3, Nat.mul_div_cancel_left (k * 3) (by decide : 0 < 4)]
ac_rfl
```

For the partner identity `4*k - k*3 = k`, peel `4*k` as `k*3 + k` first
(via `4 = 3 + 1` and `Nat.mul_add`), then `Nat.add_sub_cancel_left`:

```lean
rw [show 4 * k = k * 3 + k from by
      rw [Nat.mul_comm 4 k, show (4 : Nat) = 3 + 1 from rfl,
          Nat.mul_add, Nat.mul_one]]
exact Nat.add_sub_cancel_left (k * 3) k
```

### Pattern 6: Int-cast arithmetic over `Nat` differences

When a definition reads `def deficit (a b : Nat) : Int := (a : Int) - (b : Int)`
and you need an inequality on `deficit`, the recipe is:

1. **Reduce the goal to `Nat` form** by canceling Nat-cast layers via
   `Int.ofNat_le.mpr` / `Int.ofNat_lt.mpr`.
2. **Bridge `≤ 0` / `0 <`** with `Int.sub_nonpos_of_le` and
   `Int.sub_pos_of_lt`.
3. **Bridge `≤` between two diffs** with `Int.sub_le_sub_left` /
   `Int.sub_le_sub_right`.
4. **Cancel constants** like `((1 - 1 : Nat) : Int) = 0` via `rfl` then
   `Int.sub_zero`.

Example (`covering_match` from `CoveringSpaceCausality.lean`):

```lean
theorem covering_match
    (hMatch : pathCount ≤ transportStreams)
    (_hPathCount : 0 < pathCount) :
    topologicalDeficit pathCount transportStreams ≤ 0 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  -- (pathCount - 1) ≤ (transportStreams - 1) in Nat, cast to Int, then sub_nonpos.
  exact Int.sub_nonpos_of_le
    (Int.ofNat_le.mpr (Nat.sub_le_sub_right hMatch 1))
```

Strict version (`deficit_latency_separation`) uses `Int.ofNat_lt.mpr` plus
`Nat.sub_pos_of_lt`. Symmetric subtraction (`a - a = 0`) collapses with
`Int.sub_self`. The full set of lemma names that show up:

| Direction | Lemma |
|---|---|
| `a ≤ b → a - b ≤ 0` (Int) | `Int.sub_nonpos_of_le` |
| `b < a → 0 < a - b` (Int) | `Int.sub_pos_of_lt` |
| `a ≤ b → c - b ≤ c - a` (Int) | `Int.sub_le_sub_left` |
| Nat ≤ → Int ≤ | `Int.ofNat_le.mpr` |
| Nat < → Int < | `Int.ofNat_lt.mpr` |
| `((a : Nat) : Int) - ((a : Nat) : Int) = 0` | `Int.sub_self` |

### What still needs omega

Now genuinely the holdouts. Document with `-- TODO(rustic-church):`:

- **Pure Int linear chains spanning multiple sub/neg ops without Nat-cast
  shortcuts.** Doable but ~6 lines per step. See `meta_truth_constancy`
  in `Gnosis/TopologicalMetabolism.lean` for the working pattern.
- **Free-variable search across two unfolds with mul + sub.** E.g.
  `Gnosis/BosonPosition.lean`'s `propagator_toward_sophia`.
- **`simp + omega` cascades after `by_cases` over 4 boolean conditions.**
  Each of 16 branches has a free-variable linear-arithmetic residual after
  simp. The `by_cases h_cpu/h_gpu/h_npu/h_wasm` pattern in
  `Gnosis/HeteroMoAFabric.lean` falls here. Tractable, but each branch
  needs its own targeted Init-lemma chain.
- **Nat-sub combinator** `(a₁ - b₁) + (a₂ - b₂) ≤ (a₁ + a₂) - (b₁ + b₂)`.
  See `composite_gap_lower_bound` in `Gnosis/BrunnianScanner.lean`.

## Why this matters

The `+1` is the clinamen. The Rustic Church doctrine is: every theorem
should compose cleanly from structural induction on `Nat.succ`. omega is
honest but opaque; an explicit `Nat.sub_add_cancel h` makes the proof's
*shape* visible to the reader. When the algebra is built only from named
inductive lemmas, internal consistency reduces to "the kernel accepts the
file", and the formula's structure carries through every downstream
theorem unchanged.
