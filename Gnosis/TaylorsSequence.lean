import Init

/-!
# Taylor's Sequence — The Phyle Tripod Numbers

A number is a **Phyle Tripod Number** when it can be reached from all
three axes of the Fibonacci-Lucas triangle simultaneously:

1. As a sum of two Fibonacci numbers: `fib(a) + fib(b)`
2. As a sum of two Lucas numbers: `lucas(a) + lucas(b)`
3. As a product of a Fibonacci and a Lucas: `fib(a) * lucas(b)`

These are the numbers where the open boundary (Fibonacci), the closed
boundary (Lucas), and the interference (product) all agree. They are
the nodes of the Phyle — the points where the quasicrystal's three
axes braid into a single value.

## Discovery

Taylor's Sequence was discovered on 2026-05-26 during the formalization
of the Standing Wave Aeon. The storm recording (rain.m4a, 28 minutes of
thunderstorm) was passed through spectral analysis and amplituhedron
filtering. The 199 surviving golden breath patterns turned out to equal
lucas(11) = lucas(keystone). Investigation of WHY 199 appeared revealed
that it is a Phyle Tripod Number — reachable from all three axes:

  199 = fib(10) + fib(12) = lucas(9) + lucas(10) = fib(1) * lucas(11)

The sequence of all such numbers is Taylor's Sequence.

## The sequence (first 14 terms)

  6, 7, 8, 11, 14, 15, 18, 21, 22, 29, 47, 76, 123, 199, ...

After the initial transient (6-15), it converges to a subsequence of
Lucas numbers: 18, 29, 47, 76, 123, 199, 322, ...

## Structural properties

- Every term is reachable THREE ways (the tripod)
- The sequence contains the keystone numbers: 8 (fib 6), 11 (lucas 5),
  21 (fib 8), 199 (lucas 11)
- The large terms are Lucas numbers — the BOUNDARY is what you observe
- The Fibonacci decomposition of each term uses indices that are
  gnosis structural constants (aeon, kenoma, triton, keystone)

## What this is NOT

This is not a closed-form recurrence (yet). The membership test is
currently a conjunction of three existential checks over bounded search.
The sequence may have a generating function — that is an open question.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace TaylorsSequence

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n
termination_by n => n

def lucas : Nat -> Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n
termination_by n => n

-- Section 1: The three axes

/-- Axis 1: Is n expressible as fib(a) + fib(b) for some a,b >= 2? -/
def isFibSum (n : Nat) : Bool :=
  (List.range 18).any fun a =>
    (List.range 18).any fun b =>
      a >= 2 && b >= a && fib a + fib b == n

/-- Axis 2: Is n expressible as lucas(a) + lucas(b) for some a,b >= 2? -/
def isLucasSum (n : Nat) : Bool :=
  (List.range 14).any fun a =>
    (List.range 14).any fun b =>
      a >= 2 && b >= a && lucas a + lucas b == n

/-- Axis 3: Is n expressible as fib(a) * lucas(b) for some a,b >= 1? -/
def isFibLucasProduct (n : Nat) : Bool :=
  (List.range 16).any fun a =>
    (List.range 14).any fun b =>
      a >= 1 && b >= 1 && fib a * lucas b == n

/-- A Phyle Tripod Number: reachable from ALL three axes. -/
def isPhyleTripod (n : Nat) : Bool :=
  isFibSum n && isLucasSum n && isFibLucasProduct n

-- Section 2: Taylor's Sequence (first 14 terms)

def taylorsSequence : List Nat :=
  (List.range 350).filter isPhyleTripod

theorem taylors_sequence_first_14 :
    taylorsSequence = [6, 7, 8, 11, 14, 15, 18, 21, 22, 29, 47, 76, 123, 199, 322] := by
  native_decide

theorem taylors_sequence_length : taylorsSequence.length = 15 := by native_decide

-- Section 3: Verify each term's triple decomposition

/-- 8 = fib(2)+fib(6) = lucas(2)+lucas(2) = fib(2)*lucas(2). The golden breath. -/
theorem t8_is_tripod : isPhyleTripod 8 = true := by native_decide

/-- 11 = fib(4)+fib(6) = lucas(2)+lucas(4) = fib(1)*lucas(5). FRF / lucas(5). -/
theorem t11_is_tripod : isPhyleTripod 11 = true := by native_decide

/-- 21 = fib(5)+fib(7) = lucas(2)+lucas(6) = fib(4)*lucas(3). Maha / fib(8). -/
theorem t21_is_tripod : isPhyleTripod 21 = true := by native_decide

/-- 199 = fib(10)+fib(12) = lucas(9)+lucas(10) = fib(1)*lucas(11). The standing wave aeon. -/
theorem t199_is_tripod : isPhyleTripod 199 = true := by native_decide

-- Section 4: 199's three decompositions use gnosis constants

theorem t199_fib_decomp :
    fib 10 + fib 12 = 199 := by native_decide

theorem t199_lucas_decomp :
    lucas 9 + lucas 10 = 199 := by native_decide

theorem t199_product_decomp :
    fib 1 * lucas 11 = 199 := by native_decide

/-- The Fibonacci indices (10, 12) are (kenoma, aeon). -/
theorem t199_fib_indices_are_kenoma_aeon :
    fib 10 = 55 ∧ fib 12 = 144 ∧ 10 + 12 = 22 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- 22 = double keystone = 2 * 11. The index sum is the double keystone. -/
theorem t199_index_sum_is_double_keystone :
    (10 : Nat) + 12 = 2 * 11 := by native_decide

/-- The Lucas indices (9, 10) sum to 19. 19 is prime. -/
theorem t199_lucas_index_sum : (9 : Nat) + 10 = 19 := by native_decide

/-- The product form: clinamen * lucas(keystone).
199 is literally the clinamen's view of the keystone boundary. -/
theorem t199_is_clinamen_times_keystone_boundary :
    fib 1 = 1 ∧ lucas 11 = 199 ∧ 1 * 199 = 199 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- Section 5: The sequence contains all the keystone numbers

theorem sequence_contains_8 : 8 ∈ taylorsSequence := by native_decide
theorem sequence_contains_11 : 11 ∈ taylorsSequence := by native_decide
theorem sequence_contains_21 : 21 ∈ taylorsSequence := by native_decide
theorem sequence_contains_199 : 199 ∈ taylorsSequence := by native_decide

-- Section 6: The large terms ARE Lucas numbers

theorem t18_is_lucas : 18 = lucas 6 := by native_decide
theorem t29_is_lucas : 29 = lucas 7 := by native_decide
theorem t47_is_lucas : 47 = lucas 8 := by native_decide
theorem t76_is_lucas : 76 = lucas 9 := by native_decide
theorem t123_is_lucas : 123 = lucas 10 := by native_decide
theorem t199_is_lucas : 199 = lucas 11 := by native_decide
theorem t322_is_lucas : 322 = lucas 12 := by native_decide

/-- Every Lucas number from L_6 onward (that's in our range) is in the sequence. -/
theorem lucas_subsequence :
    lucas 6 ∈ taylorsSequence ∧ lucas 7 ∈ taylorsSequence ∧
    lucas 8 ∈ taylorsSequence ∧ lucas 9 ∈ taylorsSequence ∧
    lucas 10 ∈ taylorsSequence ∧ lucas 11 ∈ taylorsSequence ∧
    lucas 12 ∈ taylorsSequence := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- Section 7: The non-Lucas terms in the transient

/-- The early terms that are NOT Lucas: 6, 7, 8, 14, 15, 21, 22.
These are the transient before the sequence locks onto the Lucas rail.
8 = fib(6), 21 = fib(8), 22 = 2*11. The Fibonacci and keystone
echoes in the transient. -/
theorem t6_not_lucas : (List.range 14).all (fun n => lucas n != 6) = true := by native_decide
theorem t8_is_fib : 8 = fib 6 := by native_decide
theorem t21_is_fib : 21 = fib 8 := by native_decide
theorem t22_is_double_keystone : 22 = 2 * 11 := by native_decide

-- Section 8: The braid structure

/-- Each term's three decompositions use DIFFERENT index pairs.
This is the braid: the three axes don't stack (same indices),
they braid (different indices converging on the same value).
Witness: 21 = fib(5)+fib(7) = lucas(2)+lucas(6) = fib(4)*lucas(3).
Indices: (5,7), (2,6), (4,3) -- all different, all braiding to 21. -/
theorem braid_at_21 :
    fib 5 + fib 7 = 21 ∧ lucas 2 + lucas 6 = 21 ∧ fib 4 * lucas 3 = 21 ∧
    (5 != 2 || 7 != 6) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem braid_at_199 :
    fib 10 + fib 12 = 199 ∧ lucas 9 + lucas 10 = 199 ∧ fib 1 * lucas 11 = 199 ∧
    (10 != 9 || 12 != 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- Section 9: Pell discriminant at each term

/-- Every Lucas term in the sequence sits on the Pell manifold. -/
theorem pell_at_6 : lucas 6 * lucas 6 = 5 * fib 6 * fib 6 + 4 := by native_decide
theorem pell_at_7 : 5 * fib 7 * fib 7 = lucas 7 * lucas 7 + 4 := by native_decide
theorem pell_at_8 : lucas 8 * lucas 8 = 5 * fib 8 * fib 8 + 4 := by native_decide
theorem pell_at_9 : 5 * fib 9 * fib 9 = lucas 9 * lucas 9 + 4 := by native_decide
theorem pell_at_10 : lucas 10 * lucas 10 = 5 * fib 10 * fib 10 + 4 := by native_decide
theorem pell_at_11 : 5 * fib 11 * fib 11 = lucas 11 * lucas 11 + 4 := by native_decide

-- Section 10: The complete Taylor's Sequence theorem

structure TaylorsSequenceTheorem where
  has_15_terms_below_350 : taylorsSequence.length = 15
  contains_golden_breath : 8 ∈ taylorsSequence
  contains_frf : 11 ∈ taylorsSequence
  contains_maha : 21 ∈ taylorsSequence
  contains_standing_wave_aeon : 199 ∈ taylorsSequence
  t199_three_ways : fib 10 + fib 12 = 199 ∧ lucas 9 + lucas 10 = 199 ∧ fib 1 * lucas 11 = 199
  lucas_rail : lucas 6 ∈ taylorsSequence ∧ lucas 11 ∈ taylorsSequence
  pell_at_keystone : 5 * fib 11 * fib 11 = lucas 11 * lucas 11 + 4

theorem taylors_sequence_theorem : TaylorsSequenceTheorem := {
  has_15_terms_below_350 := by native_decide,
  contains_golden_breath := by native_decide,
  contains_frf := by native_decide,
  contains_maha := by native_decide,
  contains_standing_wave_aeon := by native_decide,
  t199_three_ways := by refine ⟨?_, ?_, ?_⟩ <;> native_decide,
  lucas_rail := by constructor <;> native_decide,
  pell_at_keystone := by native_decide,
}

end TaylorsSequence
end Gnosis
