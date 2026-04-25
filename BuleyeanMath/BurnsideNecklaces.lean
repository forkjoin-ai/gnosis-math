/-
  BurnsideNecklaces
  =================

  Burnside's lemma, applied to binary necklaces of small length under
  cyclic rotation.  Burnside in its usual symbolic form reads

      |X / G|  =  (1 / |G|) · Σ_{g ∈ G} |Fix(g)|.

  Applied to binary strings of length `n` under the cyclic group `C_n`
  acting by rotation: a rotation by `k` positions fixes exactly those
  strings of period dividing `gcd(k, n)`, so `|Fix(rot_k)| = 2^{gcd(k,n)}`
  and the number of distinct necklaces is

      N(n)  =  (1 / n) · Σ_{k=0}^{n-1} 2^{gcd(k, n)}.

  To stay inside `Nat` and avoid division, we witness Burnside as the
  multiplicative identity

      n · N(n)  =  Σ_{k=0}^{n-1} 2^{gcd(k, n)}.

  This file computes both sides directly:
    * the left side by enumerating all `2^n` binary strings, forming each
      orbit under the `n` rotations, picking the lex-smallest rotation as
      a canonical representative, and counting strings that equal their
      own canonical representative;
    * the right side by summing `2^{gcd(k, n)}` for k = 0, …, n-1.

  The identity is then closed by `decide` for n = 3, 4, 5, 6.

  Small-n verification table (hand-computed):
    n = 3 : orbits = 4,  Σ = 2^3 + 2^1 + 2^1                     = 12 = 3·4
    n = 4 : orbits = 6,  Σ = 2^4 + 2^1 + 2^2 + 2^1               = 24 = 4·6
    n = 5 : orbits = 8,  Σ = 2^5 + 2^1·4                         = 40 = 5·8
    n = 6 : orbits = 14, Σ = 2^6 + 2^1 + 2^2 + 2^3 + 2^2 + 2^1   = 84 = 6·14

  Honest scope
  ------------
  * This file verifies Burnside only on the specific sizes n = 3, 4, 5, 6.
    It is not a proof of Burnside as a general theorem about group actions.
  * The acting group is `C_n` (cyclic rotation) only; the dihedral group
    `D_n` (adding reflections) is not treated here.
  * There is no formal `GroupAction` structure: the orbit is built
    directly as the list of distinct rotations.

  No imports beyond `Init`.  No axioms, no `sorry`.
-/

import Init

namespace BurnsideNecklaces

-- ══════════════════════════════════════════════════════════
-- EUCLIDEAN GCD  and  NATURAL POWER
-- ══════════════════════════════════════════════════════════

/-- Fueled Euclidean gcd on `Nat`: `natGcdFuel f a b` computes `gcd(a, b)`
    using up to `f` iterations of the remainder step.  Structural recursion
    on `f` keeps the definition reducible by the kernel, so `decide` works.
    For the invocations in this file we supply `a + b + 1` fuel, which is
    always enough. -/
def natGcdFuel : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | _ + 1, 0, b => b
  | f + 1, a, b => natGcdFuel f (b % a) a

/-- Euclidean gcd on `Nat`.  `natGcd 0 n = n` witnesses the identity
    `gcd(0, n) = n`, which is essential for the Burnside sum: the term
    at `k = 0` contributes `2^{gcd(0, n)} = 2^n`, the fixed-point count
    of the identity rotation (every string is fixed). -/
def natGcd (a b : Nat) : Nat := natGcdFuel (a + b + 1) a b

/-- Natural-number exponentiation, small-case friendly. -/
def natPow (b : Nat) : Nat → Nat
  | 0     => 1
  | n + 1 => b * natPow b n

-- ══════════════════════════════════════════════════════════
-- BINARY STRING ENUMERATION
-- ══════════════════════════════════════════════════════════

/-- Prepend a fixed Bool to every list in `xs`. -/
def consAll (b : Bool) : List (List Bool) → List (List Bool)
  | []        => []
  | xs :: rs  => (b :: xs) :: consAll b rs

/-- All `2^n` binary strings of length `n`, in lexicographic-ish order
    determined by `false < true` and cons from the front. -/
def allBinStrings : Nat → List (List Bool)
  | 0     => [[]]
  | n + 1 =>
    let tail := allBinStrings n
    consAll false tail ++ consAll true tail

-- ══════════════════════════════════════════════════════════
-- CYCLIC ROTATION
-- ══════════════════════════════════════════════════════════

/-- One-step cyclic left shift: `rotate [b₀, b₁, …, bₖ] = [b₁, …, bₖ, b₀]`.
    Witnesses the generator of the `C_n` action on length-n strings. -/
def rotate : List Bool → List Bool
  | []      => []
  | b :: bs => bs ++ [b]

/-- Apply `rotate` `k` times. -/
def rotateN : Nat → List Bool → List Bool
  | 0,     xs => xs
  | k + 1, xs => rotateN k (rotate xs)

-- ══════════════════════════════════════════════════════════
-- LEXICOGRAPHIC COMPARISON  on  List Bool
-- ══════════════════════════════════════════════════════════
-- Order: false < true.  Shorter prefix < longer extension.

/-- Is `xs` lex-less-than-or-equal-to `ys`? -/
def lexLe : List Bool → List Bool → Bool
  | [],          _           => true
  | _ :: _,      []          => false
  | x :: xs,     y :: ys     =>
    match x, y with
    | false, true  => true
    | true,  false => false
    | _,     _     => lexLe xs ys

/-- Choose the lex-smaller of two lists. -/
def lexMin (xs ys : List Bool) : List Bool :=
  if lexLe xs ys then xs else ys

-- ══════════════════════════════════════════════════════════
-- ORBIT  and  CANONICAL REPRESENTATIVE
-- ══════════════════════════════════════════════════════════

/-- Collect all `n` rotations of `xs` (as a list, possibly with duplicates
    when the string has a nontrivial stabilizer).  The first entry is
    `xs` itself (rotation by 0). -/
def rotations : Nat → List Bool → List (List Bool)
  | 0,     _  => []
  | k + 1, xs => xs :: rotations k (rotate xs)

/-- Canonical representative of the orbit of `xs` under `C_n`: the
    lex-smallest element among its `n` rotations. -/
def canonical (n : Nat) (xs : List Bool) : List Bool :=
  let rec go : List (List Bool) → List Bool → List Bool
    | [],        acc => acc
    | r :: rest, acc => go rest (lexMin acc r)
  match rotations n xs with
  | []        => xs
  | r :: rest => go rest r

/-- Decidable equality for `List Bool`. -/
def listBoolEq : List Bool → List Bool → Bool
  | [],      []      => true
  | [],      _ :: _  => false
  | _ :: _,  []      => false
  | x :: xs, y :: ys => (x == y) && listBoolEq xs ys

/-- A string is a canonical orbit representative iff it equals its own
    canonical form.  Counting these gives `|X/G|`. -/
def isCanonical (n : Nat) (xs : List Bool) : Bool :=
  listBoolEq (canonical n xs) xs

/-- Count list elements that satisfy a Bool predicate. -/
def countWhere {α : Type} (p : α → Bool) : List α → Nat
  | []      => 0
  | x :: xs => (if p x then 1 else 0) + countWhere p xs

/-- Number of distinct `C_n`-orbits of length-n binary strings. -/
def countOrbits (n : Nat) : Nat :=
  countWhere (isCanonical n) (allBinStrings n)

-- ══════════════════════════════════════════════════════════
-- BURNSIDE SUM:  Σ_{k=0}^{n-1} 2^{gcd(k, n)}
-- ══════════════════════════════════════════════════════════

/-- Sum `2^{gcd(k, n)}` for `k = start, start+1, …, start+count-1`.
    Using `count` down and `start` up avoids reverse-range awkwardness. -/
def burnsideSumAux (n : Nat) : Nat → Nat → Nat
  | 0,         _     => 0
  | count + 1, start => natPow 2 (natGcd start n) + burnsideSumAux n count (start + 1)

/-- The right-hand side of Burnside: Σ_{k=0}^{n-1} 2^{gcd(k, n)}. -/
def burnsideSum (n : Nat) : Nat := burnsideSumAux n n 0

-- ══════════════════════════════════════════════════════════
-- SANITY CHECKS:  orbit counts and sums agree with hand computation
-- ══════════════════════════════════════════════════════════

theorem count_orbits_n3 : countOrbits 3 = 4 := by decide

theorem count_orbits_n4 : countOrbits 4 = 6 := by decide

theorem count_orbits_n5 : countOrbits 5 = 8 := by decide

theorem count_orbits_n6 : countOrbits 6 = 14 := by decide

theorem burnside_sum_n3 : burnsideSum 3 = 12 := by decide

theorem burnside_sum_n4 : burnsideSum 4 = 24 := by decide

theorem burnside_sum_n5 : burnsideSum 5 = 40 := by decide

theorem burnside_sum_n6 : burnsideSum 6 = 84 := by decide

-- ══════════════════════════════════════════════════════════
-- BURNSIDE'S LEMMA  (multiplicative form, division-free)
-- ══════════════════════════════════════════════════════════

/--
  Burnside for `C_3` on `Bool^3`: three rotations, four orbits,
  Σ 2^{gcd(k, 3)} = 12 = 3 · 4.
-/
theorem burnside_C3 : 3 * countOrbits 3 = burnsideSum 3 := by decide

/--
  Burnside for `C_4` on `Bool^4`: four rotations, six orbits,
  Σ 2^{gcd(k, 4)} = 24 = 4 · 6.
-/
theorem burnside_C4 : 4 * countOrbits 4 = burnsideSum 4 := by decide

/--
  Burnside for `C_5` on `Bool^5`: five rotations, eight orbits,
  Σ 2^{gcd(k, 5)} = 40 = 5 · 8.  All non-identity elements of `C_p`
  (p prime) have fixed-point count `2^1`, so the sum reduces to
  `2^p + (p - 1) · 2`.
-/
theorem burnside_C5 : 5 * countOrbits 5 = burnsideSum 5 := by decide

/--
  Burnside for `C_6` on `Bool^6`: six rotations, fourteen orbits,
  Σ 2^{gcd(k, 6)} = 2^6 + 2^1 + 2^2 + 2^3 + 2^2 + 2^1 = 84 = 6 · 14.
  The divisor structure of 6 shows up directly in the per-rotation
  fixed-point counts.
-/
theorem burnside_C6 : 6 * countOrbits 6 = burnsideSum 6 := by decide

-- ══════════════════════════════════════════════════════════
-- STRUCTURAL SANITY:  rotate is a cyclic group action of order n
-- ══════════════════════════════════════════════════════════

/-- Rotating an empty list `k` times still gives the empty list. -/
theorem rotateN_nil (k : Nat) : rotateN k [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rotateN, rotate, ih]

/-- On length-n strings, rotating n times returns the original string.
    Verified concretely for n = 3, 4, 5, 6 by enumerating all `2^n`
    strings.  A `Bool`-valued exhaustive check. -/
def allRotateNFixpoint (n : Nat) : Bool :=
  (allBinStrings n).all (fun xs => listBoolEq (rotateN n xs) xs)

theorem rotateN_fixpoint_n3 : allRotateNFixpoint 3 = true := by decide

theorem rotateN_fixpoint_n4 : allRotateNFixpoint 4 = true := by decide

theorem rotateN_fixpoint_n5 : allRotateNFixpoint 5 = true := by decide

theorem rotateN_fixpoint_n6 : allRotateNFixpoint 6 = true := by decide

-- ══════════════════════════════════════════════════════════
-- GCD SANITY
-- ══════════════════════════════════════════════════════════

theorem gcd_0_6 : natGcd 0 6 = 6 := by decide
theorem gcd_3_6 : natGcd 3 6 = 3 := by decide
theorem gcd_4_6 : natGcd 4 6 = 2 := by decide
theorem gcd_5_6 : natGcd 5 6 = 1 := by decide

end BurnsideNecklaces
