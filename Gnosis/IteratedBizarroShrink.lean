import Init

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Iterated Bizarro Shrink — How Many Times?

`bitwise/cache-fp48.ts` realizes the canonical 4:3 bitwise shrink:
`outputBits * 4 = inputBits * 3` (`64 * 3 = 48 * 4`). The 16 bits
the front-only consumer discards become the back channel of a
bi-sided cell (`bitwise/bisided-bit.ts`).

This file answers the iteration question: **how many times can we
shrink, and what does it cost?**

Three ceilings with different shapes:

1. **Strict 4:3 ceiling** — for the bit-clean shrink to hold
   without truncation, the input must be divisible by 4. From
   `64` the chain is `64 → 48 → 36 → 27`; three strict iterations
   before `27` (which is not divisible by 4) breaks the strict
   invariant. `shrinkStep_strict` and `fp64_strict_chain`.

2. **Byte-aligned ceiling** — for output to remain byte-clean
   (multiple of 8) on the wire, only one iteration survives:
   `64 → 48`. The next, `48 → 36`, is 4.5 bytes — bit-aligned but
   not byte-aligned. `fp64_byte_aligned_chain`.

3. **Conservation** — at every level, `iterShrink k n +
   totalBackChannel k n = n`. The "discarded" bits at each step are
   not lost; they are the back channel, addressable by a bi-sided
   consumer or borne as implicit context. The wire bytes shrink;
   the total bit content does not. `iterShrink_plus_total_back`.

## The fp64 chain in numbers

| Level | Front | Back at this step | Total back-channel |
|------:|------:|------------------:|-------------------:|
|     0 |    64 |                 — |                  0 |
|     1 |    48 |                16 |                 16 |
|     2 |    36 |                12 |                 28 |
|     3 |    27 |                 9 |                 37 |
|     4 |    20 |                 7 |                 44 |

After 3 strict iterations the chain has compressed `64` bits of
input to a 27-bit front plus 37 bits of context-borne back channel
(`16 + 12 + 9`). Wire bytes: 6 (fp48) → 4.5 (fp36) → 3.375 (fp27).
Effective collision resistance is preserved across the recursion
when the back channel is recoverable from the consumer's context.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace IteratedBizarroShrink

/-! ## The 4:3 shrink primitive -/

/-- A single bitwise shrink at the 4:3 invariant: `outputBits * 4 =
inputBits * 3`. The fp64 → fp48 compressor in `bitwise/cache-fp48.ts`
is the canonical witness. -/
structure BitwiseShrink where
  inputBits : Nat
  outputBits : Nat
  hShrink : outputBits * 4 = inputBits * 3
deriving Repr

/-- The canonical fp64 → fp48 shrink. -/
def fp48Shrink : BitwiseShrink :=
  { inputBits := 64
    outputBits := 48
    hShrink := by decide }

theorem fp48Shrink_inputBits : fp48Shrink.inputBits = 64 := rfl
theorem fp48Shrink_outputBits : fp48Shrink.outputBits = 48 := rfl

/-! ## Shrink as a Nat function

`shrinkStep n = ⌊n * 3 / 4⌋`. For `4 ∣ n` this is exact (the strict
invariant holds). For `¬ 4 ∣ n` integer division truncates. -/

def shrinkStep (n : Nat) : Nat := (n * 3) / 4

theorem shrinkStep_64 : shrinkStep 64 = 48 := by decide
theorem shrinkStep_48 : shrinkStep 48 = 36 := by decide
theorem shrinkStep_36 : shrinkStep 36 = 27 := by decide
theorem shrinkStep_27 : shrinkStep 27 = 20 := by decide

theorem shrinkStep_le (n : Nat) : shrinkStep n ≤ n := by
  unfold shrinkStep
  omega

theorem shrinkStep_strict (n : Nat) (h : 4 ∣ n) :
    shrinkStep n * 4 = n * 3 := by
  unfold shrinkStep
  obtain ⟨k, rfl⟩ := h
  omega

/-! ## Iterated shrink -/

def iterShrink : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterShrink k (shrinkStep n)

theorem iterShrink_0 (n : Nat) : iterShrink 0 n = n := rfl

theorem iterShrink_succ (k n : Nat) :
    iterShrink (k + 1) n = iterShrink k (shrinkStep n) := rfl

/-! ## The fp64 chain: 64 → 48 → 36 → 27 → 20 -/

theorem fp64_chain_0 : iterShrink 0 64 = 64 := rfl
theorem fp64_chain_1 : iterShrink 1 64 = 48 := by decide
theorem fp64_chain_2 : iterShrink 2 64 = 36 := by decide
theorem fp64_chain_3 : iterShrink 3 64 = 27 := by decide
theorem fp64_chain_4 : iterShrink 4 64 = 20 := by decide

/-! ## Strict 4:3 ceiling: three iterations from 64 -/

/-- The bit-clean predicate: `n` admits a strict 4:3 shrink without
truncation. -/
def isStrictShrinkable (n : Nat) : Prop := 4 ∣ n

theorem fp64_strict_chain :
    isStrictShrinkable (iterShrink 0 64)
    ∧ isStrictShrinkable (iterShrink 1 64)
    ∧ isStrictShrinkable (iterShrink 2 64)
    ∧ ¬ isStrictShrinkable (iterShrink 3 64) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 4 ∣ 64; decide
  · rw [fp64_chain_1]; show 4 ∣ 48; decide
  · rw [fp64_chain_2]; show 4 ∣ 36; decide
  · rw [fp64_chain_3]; show ¬ 4 ∣ 27; decide

/-- The 4th strict shrink truncates: `27 * 3 = 81`, not divisible by 4,
so `shrinkStep 27 * 4 = 80 < 81 = 27 * 3`. One bit is lost. -/
theorem strict_chain_breaks_at_4 :
    shrinkStep 27 * 4 + 1 = 27 * 3 := by decide

/-! ## Byte-aligned ceiling: one iteration from 64 -/

def isByteAligned (n : Nat) : Prop := 8 ∣ n

theorem fp64_byte_aligned_chain :
    isByteAligned (iterShrink 0 64)
    ∧ isByteAligned (iterShrink 1 64)
    ∧ ¬ isByteAligned (iterShrink 2 64) := by
  refine ⟨?_, ?_, ?_⟩
  · show 8 ∣ 64; decide
  · rw [fp64_chain_1]; show 8 ∣ 48; decide
  · rw [fp64_chain_2]; show ¬ 8 ∣ 36; decide

/-! ## Back channel: bits reclaimed at each step

`backChannel n = n - shrinkStep n`. For strict shrinks this equals
`n / 4`. These are the bits a fp48-style consumer discards but a
bi-sided consumer reads. -/

def backChannel (n : Nat) : Nat := n - shrinkStep n

theorem backChannel_64 : backChannel 64 = 16 := by decide
theorem backChannel_48 : backChannel 48 = 12 := by decide
theorem backChannel_36 : backChannel 36 = 9 := by decide
theorem backChannel_27 : backChannel 27 = 7 := by decide

theorem backChannel_strict (n : Nat) (h : 4 ∣ n) :
    backChannel n = n / 4 := by
  unfold backChannel shrinkStep
  obtain ⟨k, rfl⟩ := h
  omega

theorem shrinkStep_plus_backChannel (n : Nat) :
    shrinkStep n + backChannel n = n := by
  unfold backChannel
  have := shrinkStep_le n
  omega

/-! ## Total back-channel bits across `k` iterations -/

def totalBackChannel : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => backChannel n + totalBackChannel k (shrinkStep n)

theorem totalBackChannel_0 (n : Nat) : totalBackChannel 0 n = 0 := rfl

theorem totalBackChannel_succ (k n : Nat) :
    totalBackChannel (k + 1) n = backChannel n + totalBackChannel k (shrinkStep n) := rfl

theorem fp64_total_back_3 : totalBackChannel 3 64 = 37 := by decide
theorem fp64_total_back_4 : totalBackChannel 4 64 = 44 := by decide

/-! ## Conservation: front + total back = input

At every level, the iterated shrink output plus the sum of all
reclaimed back-channel bits equals the original input. The bits
are not lost; they are redistributed from on-wire payload to
context-borne metadata.
-/

theorem iterShrink_plus_total_back (n : Nat) :
    ∀ k, iterShrink k n + totalBackChannel k n = n := by
  intro k
  induction k generalizing n with
  | zero =>
    show n + 0 = n
    omega
  | succ j ih =>
    show iterShrink j (shrinkStep n)
       + (backChannel n + totalBackChannel j (shrinkStep n)) = n
    have ih_at := ih (shrinkStep n)
    have rearrange :
        iterShrink j (shrinkStep n)
          + (backChannel n + totalBackChannel j (shrinkStep n))
        = (iterShrink j (shrinkStep n) + totalBackChannel j (shrinkStep n))
          + backChannel n := by omega
    rw [rearrange, ih_at]
    exact shrinkStep_plus_backChannel n

/-- Specialization for the canonical fp64 chain: at each of the four
levels, front + total back = 64. -/
theorem fp64_conservation_0 : iterShrink 0 64 + totalBackChannel 0 64 = 64 :=
  iterShrink_plus_total_back 64 0

theorem fp64_conservation_1 : iterShrink 1 64 + totalBackChannel 1 64 = 64 :=
  iterShrink_plus_total_back 64 1

theorem fp64_conservation_2 : iterShrink 2 64 + totalBackChannel 2 64 = 64 :=
  iterShrink_plus_total_back 64 2

theorem fp64_conservation_3 : iterShrink 3 64 + totalBackChannel 3 64 = 64 :=
  iterShrink_plus_total_back 64 3

theorem fp64_conservation_4 : iterShrink 4 64 + totalBackChannel 4 64 = 64 :=
  iterShrink_plus_total_back 64 4

/-! ## Wire savings per strict step: 25%

A strict 4:3 shrink emits 3 output bits per 4 input bits, so each
strict iteration removes 1 bit per 4 input bits from the wire. -/

theorem strict_wire_savings (s : BitwiseShrink) :
    s.outputBits * 4 = s.inputBits * 3 := s.hShrink

theorem fp48_wire_savings : 48 * 4 = 64 * 3 := by decide

/-- The wire-byte ratio for a strict shrink: output / input = 3/4. -/
theorem strict_wire_ratio (s : BitwiseShrink) (h : s.inputBits > 0) :
    4 * s.outputBits = 3 * s.inputBits := by
  have := s.hShrink
  omega

/-! ## Cost-resistance bridge

When the back channel of each step is borne as implicit context
(cache namespace, recipient ID, dictionary key) rather than on the
wire, the on-wire payload shrinks while the bits that determine
collision resistance are unchanged. Conservation
(`iterShrink_plus_total_back`) is the formal witness: every input
bit ends up on one side of the front/back partition.
-/

/-- The on-wire payload after `k` strict iterations of an `n`-bit
input. -/
def wirePayload (k n : Nat) : Nat := iterShrink k n

/-- The implicit-context back-channel after `k` iterations. -/
def contextChannel (k n : Nat) : Nat := totalBackChannel k n

theorem wire_plus_context_eq_input (k n : Nat) :
    wirePayload k n + contextChannel k n = n :=
  iterShrink_plus_total_back n k

end IteratedBizarroShrink
end Gnosis
