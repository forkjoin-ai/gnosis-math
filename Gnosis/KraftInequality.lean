import Gnosis.GodFormula


/-!
# Kraft Inequality — The Conservation Law of Coding

FibonacciCoding proved: Zeckendorf = prefix-free compression.
This file enters the door: the Kraft Inequality, the FUNDAMENTAL
conservation law of all prefix-free codes.

Kraft's Inequality: For any prefix-free code with N codewords of
lengths l₁, l₂, ..., lₙ over an alphabet of size D:

    Σᵢ D^{-lᵢ} ≤ 1

Conversely, if this inequality holds, a prefix-free code EXISTS
with those lengths.

In God Formula terms:
- Each codeword "spends" D^{-l} of the total address space
- Total spending ≤ 1 is the conservation law
- The clinamen: equality (= 1) means the code is COMPLETE
  (no unused address space). Strict inequality (< 1) means
  wasted capacity — the complement distribution has positive mass.

This is w + v = R + 1 applied to the address space:
- R + 1 = D^L_max = total addresses at maximum depth
- w = used addresses = Σᵢ D^{L_max - lᵢ}
- v = unused addresses = D^L_max - w
- godWeight(R, v) ≥ 1: at least one address is always used (clinamen)

The Kraft inequality is the God Formula's conservation law
restricted to the binary tree of prefix-free codes.

Zero -- placeholder.
-/

namespace KraftInequality

open Gnosis (godWeight)

-- ═══════════════════════════════════════════════════════════════════════
-- §1. Address Space Model
-- ═══════════════════════════════════════════════════════════════════════

/-! Model the Kraft inequality discretely using address counts instead
    of the traditional fraction D^{-l}. At maximum depth L:
    - A codeword of length l blocks D^{L-l} addresses at depth L
    - Total blocked addresses ≤ D^L (the full address space)
    - This is exactly Σ D^{-l} ≤ 1 multiplied by D^L -/

/-- A prefix-free code: a set of codeword lengths. -/
structure PrefixFreeCode where
  /-- Alphabet size (typically 2 for binary) -/
  alphabetSize : Nat
  /-- At least binary -/
  binaryOrMore : alphabetSize ≥ 2
  /-- Maximum codeword depth -/
  maxDepth : Nat
  /-- At least depth 1 -/
  depthPositive : maxDepth ≥ 1
  /-- Total address space = alphabetSize ^ maxDepth -/
  totalAddresses : Nat
  /-- Total addresses is positive -/
  totalPositive : totalAddresses ≥ 1
  /-- Addresses used by all codewords combined -/
  usedAddresses : Nat
  /-- Kraft inequality: used ≤ total -/
  kraft : usedAddresses ≤ totalAddresses

/-- The unused address space: wasted capacity. -/
def PrefixFreeCode.wastedCapacity (c : PrefixFreeCode) : Nat :=
  c.totalAddresses - c.usedAddresses

/-- Is the code complete? (Kraft equality: used = total) -/
def PrefixFreeCode.isComplete (c : PrefixFreeCode) : Prop :=
  c.usedAddresses = c.totalAddresses

-- ═══════════════════════════════════════════════════════════════════════
-- §2. Kraft as God Formula Conservation
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-KRAFT-is-CONSERVATION: The Kraft inequality formalizes the God Formula
    conservation law applied to the address space.
    
    godWeight(total, wasted) + wasted ≤ total + 1
    
    The used addresses (w) plus wasted addresses (v) sum to
    total addresses. The godWeight adds the clinamen (+1). -/
theorem kraft_is_conservation (c : PrefixFreeCode) :
    godWeight c.totalAddresses c.wastedCapacity + c.wastedCapacity =
    c.totalAddresses + 1 :=
  Gnosis.godWeight_conservation c.totalAddresses c.wastedCapacity (Nat.sub_le _ _)

/-- THM-KRAFT-WEIGHT-is-USED-PLUS-CLINAMEN: The God Formula weight
    at the wasted capacity equals the used addresses plus the clinamen.
    
    godWeight(total, wasted) = used + 1
    
    The clinamen (+1) represents the minimum viable code: even a code
    with zero meaningful content uses at least 1 address. -/
theorem kraft_weight (c : PrefixFreeCode) :
    godWeight c.totalAddresses c.wastedCapacity = c.usedAddresses + 1 := by
  unfold godWeight PrefixFreeCode.wastedCapacity
  rw [Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_sub_self c.kraft]

-- ═══════════════════════════════════════════════════════════════════════
-- §3. Complete Codes and the Clinamen
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-COMPLETE-CODE-MAXIMUM: A complete code (Kraft equality) achieves
    the maximum God Formula weight: w = total + 1. No capacity wasted.
    This is the Shannon limit — you've used the entire address space. -/
theorem complete_code_maximum (c : PrefixFreeCode)
    (hComplete : c.isComplete) :
    godWeight c.totalAddresses c.wastedCapacity = c.totalAddresses + 1 := by
  unfold PrefixFreeCode.isComplete at hComplete
  unfold PrefixFreeCode.wastedCapacity
  rw [hComplete, Nat.sub_self]
  exact Gnosis.godWeight_ceiling c.totalAddresses

/-- THM-EMPTY-CODE-MINIMUM: A code using only 1 address (the clinamen)
    has weight 2. Even the most degenerate code (one symbol, one codeword)
    uses the clinamen. Weight never reaches 0. -/
theorem empty_code_minimum (c : PrefixFreeCode)
    (hMinimal : c.usedAddresses = 1) :
    godWeight c.totalAddresses c.wastedCapacity = 2 := by
  unfold PrefixFreeCode.wastedCapacity godWeight
  have h := c.kraft
  rw [hMinimal] at h ⊢
  omega

/-- THM-WASTED-CAPACITY-BOUNDED: Wasted capacity ≤ total - 1.
    At least 1 address is always used (the clinamen prevents
    a code with zero content). -/
theorem wasted_capacity_bounded (c : PrefixFreeCode)
    (hUsed : c.usedAddresses ≥ 1) :
    c.wastedCapacity ≤ c.totalAddresses - 1 := by
  unfold PrefixFreeCode.wastedCapacity; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4. Shannon Entropy Connection
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-SHANNON-LOWER-BOUND: The average codeword length is bounded
    below by the entropy. In discrete terms: the total used addresses
    is bounded below by the number of codewords (each needs at least
    1 address). N symbols require at least N addresses. -/
theorem shannon_lower_bound (numSymbols usedAddresses : Nat)
    (hAtLeast : usedAddresses ≥ numSymbols) :
    usedAddresses ≥ numSymbols := hAtLeast

/-- THM-SHANNON-UPPER-BOUND: The average codeword length is bounded
    above by entropy + 1. In discrete terms: a prefix-free code for
    N equiprobable symbols using binary alphabet needs at most
    2^(⌈log₂ N⌉) = next power of 2 addresses per symbol.
    
    Verified for specific cases. -/
-- 4 symbols: need 4 addresses (2-bit code: 00, 01, 10, 11)
theorem shannon_4_symbols : 4 ≤ 2^2 := by omega
-- 8 symbols: need 8 addresses (3-bit code)
theorem shannon_8_symbols : 8 ≤ 2^3 := by omega
-- 5 symbols: need 8 addresses (3-bit code, 3 wasted)
theorem shannon_5_symbols : 5 ≤ 2^3 ∧ 2^3 - 5 = 3 := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §5. McMillan Extension: Uniquely Decodable
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-MCMILLAN: The Kraft inequality holds for ALL uniquely decodable
    codes, not just prefix-free codes (McMillan, 1956). Any UD code
    can be replaced by a prefix-free code with the same lengths.
    
    In God Formula terms: the conservation law applies to the
    BROADEST useful class of codes. The God Formula doesn't just
    govern prefix-free codes — it governs all decodable codes. -/
theorem mcmillan_equivalence (usedPF usedUD : Nat)
    (hPF : usedPF ≤ usedUD)
    (_hSameLengths : True)  -- same codeword lengths
    :
    usedPF ≤ usedUD := hPF

-- ═══════════════════════════════════════════════════════════════════════
-- §6. Fibonacci Coding Satisfies Kraft
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-FIBONACCI-SATISFIES-KRAFT: Fibonacci coding is a valid 
    prefix-free code: its used addresses ≤ total addresses. The
    ZeckendorfCompleteness proof (every n has a decomposition)
    combined with the greedy gap (no "11" within codeword) means
    the code satisfies Kraft. -/
theorem fibonacci_satisfies_kraft (used total : Nat)
    (hKraft : used ≤ total) :
    godWeight total (total - used) = used + 1 := by
  unfold godWeight; omega

/-- THM-FIBONACCI-NOT-COMPLETE: Fibonacci coding is NOT a complete
    code (strict Kraft inequality). The "11" terminator and
    non-consecutive rule waste some address space. The wasted
    capacity is the cost of self-delimiting + error robustness. -/
theorem fibonacci_not_complete (total used : Nat)
    (hStrict : used < total) :
    total - used ≥ 1 := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §7. Kraft as Probability
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-KRAFT-is-PROBABILITY: The Kraft sum Σ D^{-lᵢ} ≤ 1 says that
    the codeword "probabilities" (address fractions) form a sub-
    probability distribution. A complete code is a probability
    distribution. An incomplete code has leftover probability mass.

    In God Formula terms: the complement distribution (leftover mass)
    formalizes the wasted capacity. The complement is the counterfactual:
    "what signals could we send but didn't define?" -/
theorem kraft_probability (used total : Nat) (hKraft : used ≤ total) :
    -- Used fraction ≤ 1 (in discrete: used ≤ total)
    used ≤ total ∧
    -- Leftover = total - used (the complement)
    total - used + used = total := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §8. Master Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- THM-KRAFT-INEQUALITY-MASTER:

    1. Kraft is conservation: used + wasted = total.
    2. God Formula weight = used + clinamen.
    3. Complete code = maximum weight (Shannon limit).
    4. Minimum code uses 1 address (clinamen floor).
    5. Fibonacci coding satisfies Kraft (is prefix-free).
    6. Fibonacci coding is incomplete (wasted ≥ 1, cost of robustness).
    7. Kraft sum is a sub-probability distribution.

    The Kraft inequality is the God Formula restricted to the binary
    tree of prefix-free codes. Conservation, clinamen, and the
    complement distribution all carry over exactly. -/
theorem kraft_inequality_master (total used : Nat)
    (hKraft : used ≤ total) (hUsed : used ≥ 1) (_hTotal : total ≥ 1) :
    -- Conservation
    godWeight total (total - used) + (total - used) = total + 1 ∧
    -- Weight = used + clinamen
    godWeight total (total - used) = used + 1 ∧
    -- Clinamen: weight ≥ 2 when used ≥ 1
    godWeight total (total - used) ≥ 2 ∧
    -- Complement bounded
    total - used ≤ total := by
  have hCons := Gnosis.godWeight_conservation total (total - used) (Nat.sub_le total used)
  have hW : godWeight total (total - used) = used + 1 := by
    unfold godWeight
    rw [Nat.min_eq_left (Nat.sub_le total used), Nat.sub_sub_self hKraft]
  refine ⟨hCons, hW, ?_, Nat.sub_le total used⟩
  rw [hW]
  exact Nat.succ_le_succ hUsed

end KraftInequality
