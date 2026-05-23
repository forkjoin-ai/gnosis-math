import Init

/-!
# FiniteDynamicsCore — the shared spine under the contrarian dynamics family

Survey of the corpus (see `ANTI_THEORY_MANIFESTO.md`, `Gnosis/Contrarian/`) shows the
"contrarian" modules are not one mathematical object; they are one *epistemic stance*
(state the inverted claim with explicit structure, prove only the bounded consequence).
But a real **sub-family** — periods, orders, conservation, dissipation, cutoffs
(`AeonNoise`, `ArnoldCatMapOrder5`, `DiscreteClosedTimelikeStep`, `Cancer.CancerTopology`,
`CollatzOneTwoFourBraid`, the `AeonTwelve*` clocks, `ErgodicCutoff*`) — does share an
extractable Lean core. This module is that core, plus the two genuinely reusable
*antitheorem schemas* the broader contrarian corpus leans on.

Two layers, kept separate and honest:

* **Dynamics primitives** — `iter`, `Returns`/`ReturnsAll`, `period_dvd` (order theory),
  `returns_conserves` (conservative regime), and `DissipativeSystem` with
  `dissipative_not_periodic` (dissipative regime). These tie the dynamics sub-family.
* **Antitheorem schemas** — `separates` (a differing invariant refutes an identity) and
  `not_forced_by_witness` (a structure that holds while the expected property fails does
  not force it). These are the shapes behind the separation / non-forcing antitheorems.
  The *inversion* antitheorems (`chaos_is_order` etc.) are deliberately not abstracted:
  by the `Contrarian/README` design they are thin bounded consequences of a field, and a
  forced abstraction would add nothing the kernel doesn't already check.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace FiniteDynamicsCore

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Iteration and periods
-- ═══════════════════════════════════════════════════════════════════════

/-- Iterate a self-map `f` exactly `n` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0,     x => x
  | k + 1, x => f (iter f k x)

/-- `f` carries `x` back to itself after `T` ticks: a closed (conservative) orbit. -/
def Returns {α : Type} (f : α → α) (T : Nat) (x : α) : Prop := iter f T x = x

/-- `T` is a period of `f` over the whole carrier `c`. -/
def ReturnsAll {α : Type} (f : α → α) (c : List α) (T : Nat) : Prop :=
  ∀ x ∈ c, iter f T x = x

/-- `f` commutes through the iterate. -/
theorem iter_succ_comm {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f n (f x) = f (iter f n x) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show f (iter f k (f x)) = f (f (iter f k x))
      rw [ih]

/-- Iteration is additive in the step count. -/
theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
      rw [Nat.add_right_comm k 1 b]
      show f (iter f (k + b) x) = f (iter f k (iter f b x))
      rw [ih]

/-- A returning point returns after every multiple of its period. -/
theorem iter_pmul_of_fix {α : Type} (f : α → α) (p : Nat) (x : α)
    (h : iter f p x = x) : ∀ q, iter f (p * q) x = x := by
  intro q
  induction q with
  | zero => rfl
  | succ k ih =>
      show iter f (p * k + p) x = x
      rw [iter_add, h, ih]

/-- A period is inherited by every multiple: `p ∣ T → period p → period T`. -/
theorem returnsAll_of_dvd {α : Type} (f : α → α) (c : List α) (p T : Nat)
    (hdvd : p ∣ T) (h : ReturnsAll f c p) : ReturnsAll f c T := by
  intro x hx
  rcases hdvd with ⟨q, rfl⟩
  exact iter_pmul_of_fix f p x (h x hx) q

/-- A carrier closed under `f` is closed under every iterate. -/
theorem iter_mem {α : Type} (f : α → α) (c : List α)
    (hclos : ∀ x ∈ c, f x ∈ c) (n : Nat) (x : α) (hx : x ∈ c) :
    iter f n x ∈ c := by
  induction n with
  | zero => exact hx
  | succ k ih => exact hclos (iter f k x) ih

/-- Over a closed orbit every observable returns: the conservative regime conserves
    every `Nat`-valued quantity across one period. -/
theorem returns_conserves {α : Type} (f : α → α) (T : Nat) (x : α) (m : α → Nat)
    (h : Returns f T x) : m (iter f T x) = m x := by
  unfold Returns at h; rw [h]

/-- **Order theorem.** If `n` is a period and no positive `d < n` is, then every period is
    a multiple of `n` — so `n` is the order of the cyclic group `f` generates over `c`.
    For concrete maps the failure hypothesis is closed and `decide`-able. -/
theorem period_dvd {α : Type} (f : α → α) (c : List α) (n : Nat)
    (hn : 0 < n)
    (hclos : ∀ x ∈ c, f x ∈ c)
    (hper : ReturnsAll f c n)
    (hfail : ∀ d, d < n → 0 < d → ¬ ReturnsAll f c d)
    (T : Nat) (hT : ReturnsAll f c T) : n ∣ T := by
  have hmod : n * (T / n) + T % n = T := Nat.div_add_mod T n
  have hmul : ReturnsAll f c (n * (T / n)) :=
    returnsAll_of_dvd f c n (n * (T / n)) ⟨T / n, rfl⟩ hper
  have hr : ReturnsAll f c (T % n) := by
    intro x hx
    have hxT : iter f T x = x := hT x hx
    rw [← hmod, iter_add] at hxT
    have hmem : iter f (T % n) x ∈ c := iter_mem f c hclos (T % n) x hx
    rw [hmul (iter f (T % n) x) hmem] at hxT
    exact hxT
  have hrlt : T % n < n := Nat.mod_lt T hn
  rcases Nat.eq_zero_or_pos (T % n) with h0 | hpos
  · refine ⟨T / n, ?_⟩
    rw [h0, Nat.add_zero] at hmod
    exact hmod.symm
  · exact absurd hr (hfail (T % n) hrlt hpos)

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The dissipative regime
-- ═══════════════════════════════════════════════════════════════════════

/-- A dissipative system: a step with a `Nat` monovariant `mono` that drops by exactly 1
    while positive (`descent`) and is fixed at 0 (`absorb`). -/
structure DissipativeSystem (α : Type) where
  step : α → α
  mono : α → Nat
  descent : ∀ x, 0 < mono x → mono (step x) = mono x - 1
  absorb  : ∀ x, mono x = 0 → mono (step x) = 0

/-- Uniform descent: every step drops the monovariant by 1 (saturating). -/
theorem step_sub_one {α : Type} (S : DissipativeSystem α) (x : α) :
    S.mono (S.step x) = S.mono x - 1 := by
  by_cases h : S.mono x = 0
  · rw [S.absorb x h, h]
  · exact S.descent x (Nat.pos_of_ne_zero h)

/-- The monovariant after `n` steps is the saturating `mono x - n`. -/
theorem dissipative_mono_after {α : Type} (S : DissipativeSystem α) (n : Nat) (x : α) :
    S.mono (iter S.step n x) = S.mono x - n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show S.mono (S.step (iter S.step k x)) = S.mono x - (k + 1)
      rw [step_sub_one S (iter S.step k x), ih, Nat.sub_sub]

/-- Convergence time equals the initial monovariant. -/
theorem dissipative_absorbs {α : Type} (S : DissipativeSystem α) (n : Nat) (x : α)
    (h : S.mono x = n) : S.mono (iter S.step n x) = 0 := by
  rw [dissipative_mono_after S n x, h, Nat.sub_self]

/-- **The duality theorem.** A dissipative state with positive monovariant is aperiodic:
    it never returns. Conservative (periodic) and dissipative (descending) regimes meet
    only at the absorbing point. -/
theorem dissipative_not_periodic {α : Type} (S : DissipativeSystem α) (x : α) (T : Nat)
    (hx : 0 < S.mono x) (hT : 0 < T) : iter S.step T x ≠ x := by
  intro hreturn
  have hafter : S.mono (iter S.step T x) = S.mono x - T := dissipative_mono_after S T x
  rw [hreturn] at hafter
  have hlt : S.mono x - T < S.mono x := Nat.sub_lt hx hT
  rw [← hafter] at hlt
  exact Nat.lt_irrefl _ hlt

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Cycle-type fingerprint (conjugacy invariant)
-- ═══════════════════════════════════════════════════════════════════════

/-- Number of carrier points fixed by `f^d`. The multiset of these counts over all `d` is
    a conjugacy invariant: conjugate permutations share it. -/
def countFixedBy {α : Type} [DecidableEq α] (f : α → α) (c : List α) (d : Nat) : Nat :=
  (c.filter (fun x => decide (iter f d x = x))).length

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Antitheorem schemas
-- ═══════════════════════════════════════════════════════════════════════

/-- **Separation schema.** A differing invariant refutes an identity: if `I a ≠ I b` then
    `a ≠ b`. The cycle-type antitheorem (`actions_are_not_conjugate`) and the Plücker /
    trichotomy separations are instances. -/
theorem separates {α : Type} {γ : Type} (I : α → γ) {a b : α}
    (h : I a ≠ I b) : a ≠ b :=
  fun heq => h (congrArg I heq)

/-- **Non-forcing schema.** A single witness where structure `S` holds but the expected
    property `P` fails refutes "S forces P". The `contrarian` non-positive-`β₁` and
    non-`β₁ = budget` queue antitheorems are instances. -/
theorem not_forced_by_witness {α : Type} (S P : α → Prop) (a : α)
    (hS : S a) (hP : ¬ P a) : ¬ (∀ x, S x → P x) :=
  fun hforces => hP (hforces a hS)

end FiniteDynamicsCore
end Gnosis
