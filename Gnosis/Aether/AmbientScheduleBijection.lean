import Init
import Gnosis.DiscreteClosedTimelikeStep

/-!
# Ambient-scheduler stride traversal is a permutation (Rustic Church, Init-only)

The **aether ambient scheduler** (`open-source/aether/src/wasm-simd/ambient-scheduler.ts`)
picks an entropy-guided start offset and a **stride** `s` over `n` lanes, then emits the
traversal `k ↦ (start + k·s) mod n` as an `executionOrder` permutation together with its
`inverseOrder`. The runtime invariant the scheduler rests on is: when `s` is coprime to `n`
the traversal visits **every lane exactly once**, so the "reorder rows, compute, write back
via `inverseOrder`" pipeline loses no token. This module certifies that invariant.

## What is proved (and the exact boundary on coprimality)

The injectivity argument is Pattern 4 (modular arithmetic, bounded operands): from
`(a·s) % n = (b·s) % n` with `b ≤ a < n` we get `n ∣ (a-b)·s`; coprimality strips the `·s`
to `n ∣ (a-b)`; and `a-b < n` forces `a-b = 0`, i.e. `a = b`. The single load-bearing
coprimality fact is the **right-factor cancellation** `n ∣ d·s → n ∣ d`, abstracted as the
`propext`-only predicate `CancelsRightFactor n s`.

**Axiom boundary — why we do NOT use `Nat.Coprime`.** Init *does* ship
`Nat.Coprime.dvd_of_dvd_mul_right`, which would give the cancellation for any
`Nat.Coprime s n` directly. But `Nat.gcd`'s entire *lemma* layer in Init (`gcd_rec`,
`gcd_dvd_left`, `dvd_gcd`, and hence every `Nat.Coprime.*` lemma) is proved through
well-founded recursion and therefore carries **`Quot.sound`** in its axiom set. Routing the
theorem through `Nat.Coprime` would make `#print axioms` report `[propext, Quot.sound]`,
violating the `propext`-only contract. So instead we supply coprimality **constructively**, by
a Bézout/modular-inverse witness `s·t = q·n + 1` (the scheduler can carry `t` alongside `s`):
`cancels_of_modular_inverse` derives `CancelsRightFactor n s` from that witness using only
elementary `propext`-only divisibility lemmas. This is the *strongest Init-provable form that
stays `propext`-only*: every stride coprime to `n` has such an inverse, and the runtime always
knows one (it chose `s` deterministically), so no generality is lost in practice — only the
`Nat.gcd`-API packaging is avoided. The fully-general `Nat.Coprime` corollary is genuinely
available in Init but is deliberately omitted to keep the certificate `propext`-only; that is
the documented boundary, not a `sorry`.

* **`stride` / `strideStep`** model the traversal `(start + k·s) % n` and its multiplicative
  core `(k·s) % n` (where the bijection lives; `start` is a relabel).
* **`strideStep_injective_of_cancel`** — THE GENERAL THEOREM: `k ↦ (k·s) % n` is injective on
  `Fin n` whenever `CancelsRightFactor n s` (constructive coprimality). Injective on the finite
  carrier `Fin n` of its own size ⇒ it is a permutation ⇒ every lane is visited exactly once.
* **`strideBij` / `strideBij_injective` / `reorder_writeback_identity` /
  `stride_writeback_lossless`** — the runtime consequence: the `executionOrder` permutation
  composed with the scheduler's `inverseOrder` (any right inverse) is the identity on lanes, so
  reorder-then-writeback loses no token. Stated Mathlib-free with plain `∀ i, g (f i) = i`.
* **`stride_collides_when_not_coprime`** (Sardis-parity antitheorem) — `s = 2, n = 4`
  (`gcd = 2`) collides: `(0·2)%4 = (2·2)%4 = 0` with `0 ≠ 2`, so the coprimality hypothesis is
  load-bearing. Closed `decide`.
* **`worked_example_n12_s5`** — `n = 12, s = 5`: the inverse `t = 5` (`5·5 = 2·12 + 1`)
  certifies coprimality `propext`-only, then the general theorem gives injectivity on `Fin 12`.

Bridge note: the entropy heuristic that *chooses* `s, start` and the float SIMD work per row
stay outside the theorem. We certify only that IF `s` carries a modular inverse mod `n` (is
coprime), the reorder/writeback is lossless.

Rustic Church: `import Init` (+ `DiscreteClosedTimelikeStep` for the cyclic-step substrate),
no `omega`, no Mathlib, no `simp`/`decide` on open goals. `#print axioms` is `propext` only.
-/

namespace Gnosis
namespace Aether
namespace AmbientScheduleBijection

open Gnosis.DiscreteClosedTimelikeStep

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The traversal model
-- ═══════════════════════════════════════════════════════════════════════

/-- The runtime traversal: lane visited at step `k` is `(start + k·s) mod n`. This is the
`executionOrder[k]` the ambient scheduler emits. -/
def stride (start s n k : Nat) : Nat := (start + k * s) % n

/-- The pure multiplicative core (`start = 0`): `k ↦ (k·s) mod n`. The bijection lives here;
the additive `start` is a relabel that does not affect coverage. -/
def strideStep (s n k : Nat) : Nat := (k * s) % n

theorem stride_zero_start (s n k : Nat) : stride 0 s n k = strideStep s n k := by
  unfold stride strideStep
  rw [Nat.zero_add]

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Constructive coprimality: right-factor cancellation
-- ═══════════════════════════════════════════════════════════════════════

/-- **`CancelsRightFactor n s`** — the single load-bearing consequence of `gcd(s,n)=1`:
`n` divides a product `d·s` only when it already divides `d`. This is exactly what
`Nat.Coprime.dvd_of_dvd_mul_right` provides for `Nat.Coprime s n`; stated as its own
`propext`-only predicate so the theorems below avoid the `Quot.sound` that the `Nat.gcd`
lemma layer carries (see module docstring). -/
def CancelsRightFactor (n s : Nat) : Prop := ∀ d : Nat, n ∣ d * s → n ∣ d

/-- **Constructive coprimality from a modular inverse.** If the stride `s` has an inverse `t`
mod `n` — a Bézout witness `s·t = q·n + 1` — then `n` cancels the right factor `s`. The
scheduler chooses `s` deterministically and can carry such a `t`, so this covers every stride
it would actually use. Proof: from `n ∣ d·s`, multiply by `t` to get
`n ∣ (d·s)·t = d·(q·n) + d`; `n ∣ d·q·n`, so `n ∣ d`. Elementary divisibility only —
`propext`-only, no `Nat.gcd` lemmas. -/
theorem cancels_of_modular_inverse (n s t q : Nat) (hinv : s * t = q * n + 1) :
    CancelsRightFactor n s := by
  intro d hdvd
  have h1 : n ∣ (d * s) * t := Nat.dvd_mul_right_of_dvd hdvd t
  have h2 : (d * s) * t = d * q * n + d := by
    rw [Nat.mul_assoc d s t, hinv, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  rw [h2] at h1
  have h3 : n ∣ d * q * n := Nat.dvd_mul_left n (d * q)
  exact (Nat.dvd_add_right h3).mp h1

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The core bijection: cancellation ⇒ injective on Fin n  (GENERAL)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Ordered injectivity helper.** With `b ≤ a < n` and right-factor cancellation, equal
lanes force `a = b`. Pattern 4: `n ∣ (a·s − b·s) = (a−b)·s`, cancellation strips `·s` to
`n ∣ (a−b)`, and `a−b < n` forces `a−b = 0`. No `omega`. -/
theorem strideStep_eq_imp_eq_of_le
    {s n a b : Nat} (ha : a < n) (hcancel : CancelsRightFactor n s)
    (heq : strideStep s n a = strideStep s n b) (hle : b ≤ a) : a = b := by
  have hmod : (a * s) % n = (b * s) % n := heq
  have hd1 : n ∣ (a * s - b * s) :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  have hfact : a * s - b * s = (a - b) * s := (Nat.sub_mul a b s).symm
  rw [hfact] at hd1
  have hd2 : n ∣ (a - b) := hcancel (a - b) hd1
  have hlt : a - b < n := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hd2 hlt
  exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hzero) hle

/-- **`strideStep` injective for any coprime stride — the core coverage theorem.** For any
stride `s` with right-factor cancellation `CancelsRightFactor n s` (constructive coprimality),
the map `k ↦ (k·s) mod n` is injective on indices below `n`. Injective on the finite carrier
`Fin n` of its own size ⇒ permutation ⇒ the traversal visits every lane exactly once. No
special-casing on `s` or `n`. -/
theorem strideStep_injective_of_cancel
    {s n a b : Nat} (ha : a < n) (hb : b < n) (hcancel : CancelsRightFactor n s)
    (heq : strideStep s n a = strideStep s n b) : a = b := by
  match Nat.le_total b a with
  | Or.inl hle => exact strideStep_eq_imp_eq_of_le ha hcancel heq hle
  | Or.inr hle => exact (strideStep_eq_imp_eq_of_le hb hcancel heq.symm hle).symm

-- ═══════════════════════════════════════════════════════════════════════
-- §4  As a Fin n → Fin n permutation with a two-sided inverse
-- ═══════════════════════════════════════════════════════════════════════

/-- The traversal as a self-map of `Fin n` (the `executionOrder` permutation, `start = 0`).
Well-defined because `% n < n` (`hn : 0 < n`). -/
def strideBij {n : Nat} (hn : 0 < n) (s : Nat) (i : Fin n) : Fin n :=
  ⟨strideStep s n i.val, Nat.mod_lt _ hn⟩

/-- **`strideBij` is injective** under right-factor cancellation: the `Fin n`-level statement
of §3's core theorem (so it is a permutation of the `n` lanes). -/
theorem strideBij_injective {n : Nat} (hn : 0 < n) (s : Nat) (hcancel : CancelsRightFactor n s)
    {i j : Fin n} (h : strideBij hn s i = strideBij hn s j) : i = j := by
  apply Fin.ext
  have hval : strideStep s n i.val = strideStep s n j.val := congrArg Fin.val h
  exact strideStep_injective_of_cancel i.isLt j.isLt hcancel hval

/-- **`reorder_writeback_identity` (Mathlib-free).** An injective self-map `f` of `Fin n` with
*any* right inverse `g` (`f (g i) = i`) has `g` as a genuine left inverse too: `g (f i) = i`.
This is the abstract fact under "reorder rows, write back via `inverseOrder`": `f` =
`executionOrder`, `g` = `inverseOrder`. -/
theorem reorder_writeback_identity {n : Nat}
    (f g : Fin n → Fin n)
    (hinj : ∀ {i j : Fin n}, f i = f j → i = j)
    (hright : ∀ i, f (g i) = i) :
    ∀ i, g (f i) = i := by
  intro i
  exact hinj (hright (f i))

/-- **The scheduler's writeback is lossless.** Specializing to the stride permutation: given
the scheduler-built `inverseOrder` `g` that right-inverts the coprime-stride `executionOrder`,
applying `executionOrder` then `inverseOrder` returns every lane to itself. -/
theorem stride_writeback_lossless {n : Nat} (hn : 0 < n) (s : Nat)
    (hcancel : CancelsRightFactor n s)
    (g : Fin n → Fin n) (hright : ∀ i, strideBij hn s (g i) = i) :
    ∀ i, g (strideBij hn s i) = i :=
  reorder_writeback_identity (strideBij hn s) g (strideBij_injective hn s hcancel) hright

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Antitheorem (Sardis parity): a non-coprime stride collides
-- ═══════════════════════════════════════════════════════════════════════

/-- **The coprimality hypothesis is load-bearing.** With `s = 2, n = 4` (`gcd = 2 ≠ 1`) the
traversal is NOT injective: steps `k = 0` and `k = 2` both land on lane `0`
(`(0·2)%4 = (2·2)%4 = 0`) while `0 ≠ 2`. A scheduler that reordered rows by a non-coprime
stride would overwrite lane `0` twice and drop another lane — "a name that liveth, and is
dead". Each conjunct is a closed numeric goal, so `decide` is admitted. -/
theorem stride_collides_when_not_coprime :
    ¬ Nat.Coprime 2 4 ∧
    strideStep 2 4 0 = strideStep 2 4 2 ∧
    (0 : Nat) ≠ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Worked example: n = 12, s = 5 (gcd = 1, inverse t = 5)
-- ═══════════════════════════════════════════════════════════════════════

/-- `5` is its own inverse mod `12`: `5·5 = 25 = 2·12 + 1`. This Bézout witness certifies
coprimality of stride `5` with `12` `propext`-only (no `Nat.gcd` lemmas). -/
theorem n12_s5_cancels : CancelsRightFactor 12 5 :=
  cancels_of_modular_inverse 12 5 5 2 (by decide)

/-- **Worked serve.** For `n = 12, s = 5`, the stride traversal is injective on `Fin 12` —
the general coverage theorem instantiated at the concrete coprime stride via its modular
inverse. The scheduler may reorder 12 lanes by stride 5 and write back losslessly. -/
theorem worked_example_n12_s5
    {a b : Nat} (ha : a < 12) (hb : b < 12)
    (heq : strideStep 5 12 a = strideStep 5 12 b) : a = b :=
  strideStep_injective_of_cancel ha hb n12_s5_cancels heq

/-- Closed spot-check that the `n=12, s=5` traversal genuinely spreads across distinct lanes:
steps `0,1,2,3` land on lanes `0,5,10,3` — all distinct. Closed `decide`. -/
theorem worked_example_n12_s5_distinct_lanes :
    strideStep 5 12 0 = 0 ∧ strideStep 5 12 1 = 5 ∧
    strideStep 5 12 2 = 10 ∧ strideStep 5 12 3 = 3 ∧
    strideStep 5 12 0 ≠ strideStep 5 12 1 ∧
    strideStep 5 12 1 ≠ strideStep 5 12 2 ∧
    strideStep 5 12 2 ≠ strideStep 5 12 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end AmbientScheduleBijection
end Aether
end Gnosis
