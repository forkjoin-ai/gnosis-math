import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannUniversality

/-
  AckermannMonotone.lean
  ======================

  Discharges the one obligation recorded in `AckermannUniversality`:
  the classical Ackermann-is-not-primitive-recursive universal — the Ackermann
  diagonal eventually strictly dominates EVERY fixed hyperoperation level
  (every primitive-recursive ladder rung). This was the single deferred leg of
  the "Ackermann ceiling occupies the role of c" program
  (`AckermannLightConeBridge`, `AckermannIsLightSpeed`); it is now a theorem.

  ## The obstacle and how it is handled

  This `hyperop` has an IRREGULAR base: `hyperop 2 a 0 = 0` (the `a·0 = 0`
  multiplicative identity), so the usual Ackermann monotonicity tower — which
  relies on a uniform positive base — breaks at the level-2 corner. The fix:
  with `1 ≤ a`, the hyperoperation is zero ONLY at `(2, a, 0)` (`pos`), and the
  level-1→2 step can decrease only at `b ∈ {0, 1}` (the `(2,2)` fixed point
  `2+2 = 2·2`), so level monotonicity is stated for `b ≥ 2`.

  The tower:
    `pos`         — hyperop is positive off the level-2 corner.
    `lt_self`     — strict identity bound `b < hyperop level a b` off the corner.
    `mono_b_step` — strict one-step monotonicity in the third argument.
    `mono_b`      — monotonicity in the third argument.
    `level_le`    — level monotonicity (non-strict, `b ≥ 2`).
    `level_mono`  — many-level monotonicity.
    `eventual_domination` — the diagonal strictly dominates level `k` for
                            `n ≥ k + 3`.

  Init + the diagonal + the closed forms. Zero `sorry`, zero new `axiom`.
-/

namespace AckermannMonotone

open AckermannFunction
open AckermannUniversality

/-- With `1 ≤ a`, hyperop is zero ONLY at the level-2 corner `(2,a,0)`. -/
theorem pos (level a b : Nat) :
    1 ≤ a → ¬(level = 2 ∧ b = 0) → 1 ≤ hyperop level a b := by
  induction level, a, b using hyperop.induct with
  | case1 x b => intro _ _; simp only [hyperop]; omega
  | case2 a => intro ha _; simp only [hyperop]; omega
  | case3 x => intro _ hbad; exact absurd ⟨rfl, rfl⟩ hbad
  | case4 n x => intro _ _; simp only [hyperop]; omega
  | case5 n a b ih1 ih2 =>
    intro ha _
    simp only [hyperop]
    apply ih2 ha
    intro hbad
    obtain ⟨hn2, hX0⟩ := hbad
    subst hn2
    have hXpos : 1 ≤ hyperop (2 + 1) a b := ih1 ha (by omega)
    omega

/-- Levels ≥ 2 at third arg 1 evaluate to `a`. -/
theorem arg_one (n a : Nat) : hyperop (n + 2) a 1 = a := by
  induction n with
  | zero => rw [hyperop_two]; omega
  | succ n ih =>
    have e0 : hyperop (n + 3) a 0 = 1 := hyperop.eq_4 a n
    have e5 : hyperop (n + 3) a 1 = hyperop (n + 2) a (hyperop (n + 3) a 0) := by
      simpa using hyperop.eq_5 a (n + 2) 0
    show hyperop (n + 3) a 1 = a
    rw [e5, e0, ih]

/-- Strict identity bound: with `2 ≤ a`, off the level-2 corner the
    hyperoperation strictly exceeds its third argument. -/
theorem lt_self (level a b : Nat) :
    2 ≤ a → ¬(level = 2 ∧ b = 0) → b < hyperop level a b := by
  induction level, a, b using hyperop.induct with
  | case1 x b => intro _ _; simp only [hyperop]; omega
  | case2 a => intro ha _; simp only [hyperop]; omega
  | case3 x => intro _ hbad; exact absurd ⟨rfl, rfl⟩ hbad
  | case4 n x => intro _ _; simp only [hyperop]; omega
  | case5 n a b ih1 ih2 =>
    intro ha _
    rcases n with _ | _ | m
    · show b.succ < hyperop 1 a b.succ
      rw [hyperop_one]; omega
    · show b.succ < hyperop 2 a b.succ
      rw [hyperop_two]
      have h2 : 2 * b.succ ≤ a * b.succ := Nat.mul_le_mul ha (Nat.le_refl b.succ)
      omega
    · rw [hyperop.eq_5]
      have hbX : b < hyperop (m + 2 + 1) a b := ih1 ha (by omega)
      have hXlt : hyperop (m + 2 + 1) a b
            < hyperop (m + 2) a (hyperop (m + 2 + 1) a b) := by
        apply ih2 ha
        intro hbad
        obtain ⟨hm2, hX0⟩ := hbad
        have hm : m = 0 := by omega
        subst hm
        have hp : 1 ≤ hyperop (0 + 1 + 1 + 1) a b := pos _ a b (by omega) (by omega)
        omega
      omega

/-- Strict one-step monotonicity in the third argument (`a ≥ 2`, corner-free). -/
theorem mono_b_step (level a b : Nat) (ha : 2 ≤ a) :
    hyperop level a b < hyperop level a (b + 1) := by
  rcases level with _ | level
  · show hyperop 0 a b < hyperop 0 a (b + 1)
    rw [hyperop.eq_1, hyperop.eq_1]; omega
  · rw [hyperop.eq_5]
    refine lt_self level a (hyperop (level + 1) a b) ha ?_
    intro hbad
    obtain ⟨hl2, hX0⟩ := hbad
    subst hl2
    have hp : 1 ≤ hyperop (2 + 1) a b := pos (2 + 1) a b (by omega) (by omega)
    omega

/-- Monotonicity in the third argument (additive form). -/
theorem mono_b_add (level a c k : Nat) (ha : 2 ≤ a) :
    hyperop level a c ≤ hyperop level a (c + k) := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have h2 : hyperop level a (c + k) < hyperop level a (c + k + 1) :=
      mono_b_step level a (c + k) ha
    have : c + (k + 1) = c + k + 1 := by omega
    rw [this]; omega

/-- Monotonicity in the third argument. -/
theorem mono_b (level a c d : Nat) (ha : 2 ≤ a) (h : c ≤ d) :
    hyperop level a c ≤ hyperop level a d := by
  have hk : d = c + (d - c) := by omega
  rw [hk]; exact mono_b_add level a c (d - c) ha

/-- Level monotonicity (non-strict). Requires `b ≥ 2`: at `b ∈ {0,1}` the
    level-1→2 step can decrease (`a + b ≥ a · b`), the `(2,2)`-fixed-point
    degeneracy. -/
theorem level_le (m a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    hyperop m a b ≤ hyperop (m + 1) a b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [show hyperop (m + 1) a (b' + 1) = hyperop m a (hyperop (m + 1) a b')
        from hyperop.eq_5 a m b']
  have hY : b' + 1 ≤ hyperop (m + 1) a b' := by
    have := lt_self (m + 1) a b' ha (by omega)
    omega
  exact mono_b m a (b' + 1) (hyperop (m + 1) a b') ha hY

/-- Level monotonicity across many levels (non-strict), `b ≥ 2`. -/
theorem level_mono (k k' a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) (h : k ≤ k') :
    hyperop k a b ≤ hyperop k' a b := by
  obtain ⟨j, rfl⟩ : ∃ j, k' = k + j := ⟨k' - k, by omega⟩
  clear h
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    have step : hyperop (k + j) a b ≤ hyperop (k + j + 1) a b := level_le (k + j) a b ha hb
    have : k + (j + 1) = k + j + 1 := by omega
    rw [this]; exact Nat.le_trans ih step

/-- **THE PRIZE.** The Ackermann diagonal eventually strictly dominates every
    fixed hyperoperation level: for `n ≥ k + 3`, `hyperop k n n < A(n)`. This is
    the classical "Ackermann is not primitive recursive" universal, on the
    hyperoperation ladder. -/
theorem eventual_domination (k : Nat) :
    ∀ n, k + 3 ≤ n → hyperop k n n < ackermannDiag n := by
  intro n hn
  show hyperop k n n < hyperop n n n
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 3 := ⟨n - 3, by omega⟩
  have hchain : hyperop k (p + 3) (p + 3) ≤ hyperop (p + 2) (p + 3) (p + 3) :=
    level_mono k (p + 2) (p + 3) (p + 3) (by omega) (by omega) (by omega)
  have htop : hyperop (p + 2) (p + 3) (p + 3) < hyperop (p + 3) (p + 3) (p + 3) := by
    rw [show hyperop (p + 3) (p + 3) (p + 3)
          = hyperop (p + 2) (p + 3) (hyperop (p + 3) (p + 3) (p + 2))
          from hyperop.eq_5 (p + 3) (p + 2) (p + 2)]
    have hZlb : (p + 3) * (p + 2) ≤ hyperop (p + 3) (p + 3) (p + 2) := by
      have h := level_mono 2 (p + 3) (p + 3) (p + 2) (by omega) (by omega) (by omega)
      rwa [hyperop_two] at h
    have hZbig : (p + 3) + 1 ≤ hyperop (p + 3) (p + 3) (p + 2) := by
      have h3 : 3 * (p + 2) ≤ (p + 3) * (p + 2) := Nat.mul_le_mul (by omega) (Nat.le_refl _)
      omega
    have hs : hyperop (p + 2) (p + 3) (p + 3) < hyperop (p + 2) (p + 3) ((p + 3) + 1) :=
      mono_b_step (p + 2) (p + 3) (p + 3) (by omega)
    have hm : hyperop (p + 2) (p + 3) ((p + 3) + 1)
          ≤ hyperop (p + 2) (p + 3) (hyperop (p + 3) (p + 3) (p + 2)) :=
      mono_b (p + 2) (p + 3) ((p + 3) + 1) (hyperop (p + 3) (p + 3) (p + 2)) (by omega) hZbig
    omega
  omega

/-- The recorded obligation in `AckermannUniversality`, now DISCHARGED. -/
theorem eventualLevelDomination_holds :
    ackermannUniversalityObligation.eventualLevelDomination :=
  fun k => ⟨k + 3, eventual_domination k⟩

end AckermannMonotone
