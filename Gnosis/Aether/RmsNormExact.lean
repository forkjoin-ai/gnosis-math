import Init

/-!
# RMSNorm argmax invariance (Rustic Church, Init-only)

The **RMSNorm pilot** for the aether / wasm-simd *kernel-certificate* effort. A
kernel certificate is a `lake build`-checked, `omega`-free, Mathlib-free proof
that a numerical kernel preserves the only property a downstream consumer reads.
For an *argmax-only* consumer (next-token prediction, classification head, any
`argmax`-reading decode) the property is: **the predicted index does not move.**

RMSNorm computes `y_c = (x_c / rms(x)) * g_c`, where the normalizer
`1 / rms(x) = 1 / sqrt(mean(x^2) + eps)` is a **single positive scalar** applied
to every channel `c`. The float `sqrt` / reciprocal that produces that scalar is
**outside** every theorem here, by the bridge rule: we never claim the kernel
computes the real-number normalizer correctly. What we *do* certify is the
algebraic invariant the certificate rests on — multiplying an entire score
vector by one positive scalar `s` cannot change which coordinate is largest. So
an argmax-only consumer may **defer or skip** the RMSNorm normalizer entirely:
the predicted token is identical with or without it.

Logits / pre-argmax scores are modelled as scaled integers (`Int`) over a finite
channel index. This is faithful: the argmax decision is scale-invariant, so
integers carry the proof with no loss, `omega`-free. (Per-channel learned gain
`g_c` is a *separate* affine factor and is deliberately NOT folded in here — only
the shared normalizer scalar is, which is exactly the piece RMSNorm adds over a
bare linear head. The antitheorem below shows that a *per-channel* / non-uniform
scale, or a non-positive scale, CAN flip the argmax — so the
positivity-and-uniformity hypothesis is load-bearing, not decorative.)

Init-only discipline (named `Int`/`Nat` lemmas from `RUSTIC_CHURCH.md`,
**no `omega`**, no Mathlib, no `simp`/`decide` on open-variable goals). The core
invariant closes one line per pair via `Int.mul_lt_mul_of_pos_left`.
-/

namespace Gnosis
namespace Aether
namespace RmsNormExact

/-- `i` is the strict argmax of the scaled-integer score vector `L`: every other
channel scores strictly lower. This is the predicted-index criterion an
argmax-only decode reads — the same vocabulary as
`Gnosis.QualityMarginCacheAdmissibility.IsStrictArgmax`. -/
def IsStrictArgmax {n : Nat} (L : Fin n → Int) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → L j < L i

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The core RMSNorm invariant (uniform positive scale preserves argmax)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Uniform-scale argmax invariance — the core RMSNorm certificate.** For any
*single* positive scalar `s` (this is RMSNorm's normalizer `1 / rms(x) > 0`),
scaling every channel by `s` leaves the strict argmax fixed.

The kernel meaning: RMSNorm's normalizer is one positive number applied to the
whole vector, so it cannot move the predicted token. An argmax-only consumer may
therefore skip / defer the normalizer with no change to its output. Proof is one
line per runner-up pair: `Int.mul_lt_mul_of_pos_left (hi j hj) hs`. No `omega`. -/
theorem uniform_scale_preserves_argmax {n : Nat} (L : Fin n → Int) (i : Fin n)
    (s : Int) (hs : 0 < s) (hi : IsStrictArgmax L i) :
    IsStrictArgmax (fun j => s * L j) i := by
  intro j hj
  exact Int.mul_lt_mul_of_pos_left (hi j hj) hs

/-- A *non-positive* scalar is not enough: if `s = 0` the scaled vector is
flat (every channel `0`) and nothing is a strict argmax. Recorded as the
positivity boundary of the invariant — the antitheorem in §4 makes it concrete
on a literal witness. -/
theorem zero_scale_destroys_argmax {n : Nat} (L : Fin n → Int) (i j : Fin n)
    (_hj : j ≠ i) :
    ¬ ((fun j => (0 : Int) * L j) j < (fun j => (0 : Int) * L j) i) := by
  intro h
  -- both sides reduce to 0 * _, i.e. 0 < 0, impossible
  have h0 : (0 : Int) < 0 := by
    have e1 : (0 : Int) * L j = 0 := Int.zero_mul (L j)
    have e2 : (0 : Int) * L i = 0 := Int.zero_mul (L i)
    rw [show ((fun j => (0 : Int) * L j) j) = (0 : Int) * L j from rfl, e1,
        show ((fun j => (0 : Int) * L j) i) = (0 : Int) * L i from rfl, e2] at h
    exact h
  exact Int.lt_irrefl 0 h0

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Integer-faithful "rms is monotone in magnitude"
-- ═══════════════════════════════════════════════════════════════════════

/-- **`sumSq_monotone`.** The squaring step inside `rms(x) = sqrt(mean(x^2))` is
monotone on non-negative magnitudes: `a ≤ b → a*a ≤ b*b`. This is the clean,
integer-faithful piece of "rms grows with magnitude" — the float `sqrt`/`mean`
stay outside the theorem per the bridge rule. Closes via `Nat.mul_le_mul`. -/
theorem sumSq_monotone (a b : Nat) (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Concrete worked witness (a 3-channel uniform-scale serve)
-- ═══════════════════════════════════════════════════════════════════════

/-! Pre-norm scores `[5, 1, 0]`: channel 0 is the strict argmax. RMSNorm applies
the single positive normalizer scalar `s = 3` (a stand-in for a positive
`1 / rms(x)` after integer scaling), giving `[15, 3, 0]`. The witness routes
through `uniform_scale_preserves_argmax`, so it is a live carrier of the general
theorem, not a standalone recompute. -/

/-- Pre-RMSNorm scores of the worked example. The out-of-range arm is refuted
Init-only (`3 ≤ k + 3`), not by `omega`/`decide` on the open index. -/
def exL : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Channel 0 is the strict argmax of the pre-norm scores. -/
theorem ex_true_argmax : IsStrictArgmax exL ⟨0, by decide⟩ := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) < 5; decide
  | ⟨2, _⟩ => show (0 : Int) < 5; decide

/-- **The worked serve.** After the single positive normalizer scalar `s = 3`,
channel 0 is still the strict argmax of `fun j => 3 * exL j` — routed through the
general invariant, the predicted channel is unchanged by RMSNorm. -/
theorem ex_scaled_argmax : IsStrictArgmax (fun j => 3 * exL j) ⟨0, by decide⟩ :=
  uniform_scale_preserves_argmax exL ⟨0, by decide⟩ 3 (by decide) ex_true_argmax

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Antitheorem (Sardis parity: positivity + uniformity is load-bearing)
-- ═══════════════════════════════════════════════════════════════════════

/-! The bound is tight in *two* ways, both proved on a literal `Fin 2` witness
`[2, 1]` (channel 0 wins):

* a **non-uniform / per-channel** scale `[0, 5]` (multiply channel 0 by `0`,
  channel 1 by `5`) flips the argmax to channel 1 — so RMSNorm's *single shared*
  scalar is essential; a per-channel gain is NOT covered by this certificate;
* a single **negative** scalar `s = -1` also flips the argmax — so the
  *positivity* of the normalizer is essential.

This is the formal signature of "a name that liveth, and is dead": a kernel that
claims argmax-invariance under a scale that is not a single positive scalar would
serve the wrong token. Each conjunct is a *closed* goal (literal `Fin 2`
vectors), so `decide` is admitted by the Rustic Church contract. -/

/-- Pre-norm scores of the flip witness: channel 0 wins `[2, 1]`. -/
def antiL : Fin 2 → Int := fun k => match k with
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨_ + 2, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 _))

/-- Per-channel (non-uniform) scaled scores: channel 0 by `0`, channel 1 by `5`,
giving `[0, 5]` — now channel 1 wins. -/
def antiNonUniform : Fin 2 → Int := fun k => match k with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 5
  | ⟨_ + 2, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 _))

/--
**Sharpness.** The positivity-and-uniformity hypothesis of
`uniform_scale_preserves_argmax` is load-bearing. The pre-norm vector `antiL`
has channel 0 as its strict argmax, but:

* a *non-uniform* per-channel scale (`antiNonUniform = [0, 5]`) no longer has
  channel 0 as the strict argmax (channel 1 wins);
* the *negative* uniform scale `s = -1` (giving `[-2, -1]`) also no longer has
  channel 0 as the strict argmax.

So neither a per-channel gain nor a non-positive scalar is covered — only RMSNorm's
single positive normalizer scalar is, which is exactly what §1 certifies. -/
theorem scale_can_flip_when_not_uniform_positive :
    IsStrictArgmax antiL ⟨0, by decide⟩ ∧
    ¬ IsStrictArgmax antiNonUniform ⟨0, by decide⟩ ∧
    ¬ IsStrictArgmax (fun j => (-1 : Int) * antiL j) ⟨0, by decide⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    match j with
    | ⟨0, _⟩ => exact absurd rfl hj
    | ⟨1, _⟩ => show (1 : Int) < 2; decide
  · intro hcontra
    have hgt := hcontra ⟨1, by decide⟩ (by decide)
    exact absurd hgt (by show ¬ ((5 : Int) < 0); decide)
  · intro hcontra
    have hgt := hcontra ⟨1, by decide⟩ (by decide)
    -- hgt : (-1) * antiL ⟨1⟩ < (-1) * antiL ⟨0⟩, i.e. -1 < -2
    exact absurd hgt (by show ¬ ((-1 : Int) < -2); decide)

end RmsNormExact
end Aether
end Gnosis
