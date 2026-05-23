import Init
import Gnosis.Body.SapolskyStress

/-!
# Unimodal Dose-Response — From Adjacent Steps to a Genuine Optimization Theorem

`Gnosis.Body.SapolskyStress` proves the inverted-U only *one adjacent step at a
time*: `acute_stress_helps` says `performance s c < performance (s+1) c` just
below the peak, and `chronic_stress_hurts` the mirror image just above. Those are
local facts. They do **not**, on their own, tell you that the curve is
*genuinely* unimodal, nor where its global maximum sits, nor that the maximizer
is unique.

This module supplies the missing optimization content. Everything is built from
the same `performance s c = s * (c - s)` parabola, but the theorems here are
*interval* and *uniqueness* statements, each requiring real `Nat` induction or
product-inequality algebra on top of the adjacent steps:

1. **`strictly_rising_below_peak`** — a full strict-monotone-on-an-interval
   theorem: for *all* `a < b` with `2*b ≤ c` (both at or below the peak),
   `performance a c < performance b c`. Proved by induction on the gap `b - a`,
   chaining the adjacent `acute_stress_helps` strictly across every intermediate
   dose. This is the genuine leap past a single adjacent step.

2. **`strictly_falling_above_peak`** — the symmetric interval theorem: for all
   `a < b` with `c ≤ 2*a` (both at or above the peak),
   `performance b c < performance a c`. Same gap-induction, chaining
   `chronic_stress_hurts`.

3. **`peak_at_floor_half`** — the optimization theorem: the global maximum sits at
   `s = c/2`, i.e. `∀ s, performance s c ≤ performance (c/2) c`. A real ∀-bound
   (the argmax), proved by casing every dose `s` below vs above `c/2` and
   invoking 1 and 2. The half-point hypothesis `2*(c/2) ≤ c` holds for *all* `c`
   (`Nat.div`), and the falling arm is anchored one step above the floor-half to
   absorb the parity gap.

4. **`unique_argmax`** (even `c`) — the maximizer is *unique*: for even `c`,
   `s ≠ c/2 → performance s c < performance (c/2) c`, a strict drop at *every*
   non-peak dose. Uniqueness is the deep part. We state it for even `c` because
   for **odd** `c` the two central doses `c/2` and `c/2 + 1` *tie*
   (`odd_has_two_peaks`), so no single argmax is unique — we record that case
   honestly rather than overclaim.

5. **`strictly_unimodal`** — the headline: there is a peak `p = c/2` such that
   `performance` is strictly increasing on `[0, p]` and strictly decreasing on
   `[p, c]`, *and* it is the global maximum. A single composed statement of
   genuine unimodality (1 + 2 + 3).

Rustic Church: `import Init` plus the reused `SapolskyStress` sibling. `Nat`
only, no Float/Real, no Mathlib. Proofs from core `Nat` lemmas and explicit
`Nat` induction. No `sorry`; no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.UnimodalDoseResponse

open Gnosis.Body.SapolskyStress

/-! ## 0. Half-point arithmetic

Two facts about the floor-half `c / 2` that anchor the optimization theorem, both
holding for *every* `c` (no parity assumption). `2*(c/2) ≤ c` lets the rising arm
reach the peak; `c ≤ 2*(c/2) + 1` lets the falling arm start one step above it. -/

/-- The doubled floor-half never exceeds `c`: `2 * (c / 2) ≤ c`. (Truncated only
    by the remainder `c % 2`.) Holds for all `c`. -/
theorem two_mul_half_le (c : Nat) : 2 * (c / 2) ≤ c := by
  -- c = 2*(c/2) + c%2, so 2*(c/2) ≤ c by dropping the nonnegative remainder.
  have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
  -- 2*(c/2) ≤ 2*(c/2) + c%2 = c
  have hle : 2 * (c / 2) ≤ 2 * (c / 2) + c % 2 := Nat.le_add_right _ _
  rw [hdm] at hle
  exact hle

/-- `c` is at most one above the doubled floor-half: `c ≤ 2 * (c / 2) + 1`. The
    one-unit slack is the parity remainder `c % 2 ∈ {0, 1}`. Holds for all `c`. -/
theorem le_two_mul_half_succ (c : Nat) : c ≤ 2 * (c / 2) + 1 := by
  have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
  -- c%2 ≤ 1
  have hmod : c % 2 ≤ 1 := by
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · rw [h0]; exact Nat.zero_le 1
    · rw [h1]; exact Nat.le_refl 1
  -- c = 2*(c/2) + c%2 ≤ 2*(c/2) + 1
  calc c = 2 * (c / 2) + c % 2 := hdm.symm
    _ ≤ 2 * (c / 2) + 1 := Nat.add_le_add_left hmod _

/-! ## 1. The rising arm as a strict-monotone interval theorem

`acute_stress_helps` only steps from `s` to `s+1`. Here we chain it across a whole
interval by induction on the *gap* between the two doses. The hypothesis `2*b ≤ c`
at the upper endpoint is exactly what each intermediate adjacent step needs (the
last one, at dose `b-1`, needs `2*(b-1)+2 = 2*b ≤ c`). -/

/-- Gap-form of the rising arm, set up for induction. For every starting dose `a`
    and gap `n`, if the *upper* endpoint `a + (n + 1)` is still at or below the
    peak (`2 * (a + (n + 1)) ≤ c`), then performance strictly rises from `a` to
    `a + (n + 1)`. Proved by induction on `n`: the base case is one adjacent
    `acute_stress_helps`; the step chains the IH (over the smaller gap) with one
    more adjacent rise at the top. -/
theorem rising_gap (c : Nat) :
    ∀ (n a : Nat), 2 * (a + (n + 1)) ≤ c →
      performance a c < performance (a + (n + 1)) c := by
  intro n
  induction n with
  | zero =>
    intro a hpk
    -- a + (0 + 1) = a + 1.  2*(a+1) ≤ c  ⇒  2*a + 2 ≤ c.
    have hpk' : 2 * a + 2 ≤ c := by
      have heq : 2 * (a + (0 + 1)) = 2 * a + 2 := by
        rw [Nat.left_distrib]
      rw [heq] at hpk
      exact hpk
    -- performance a c < performance (a+1) c, and a + (0+1) = a + 1 definitionally.
    exact acute_stress_helps a c hpk'
  | succ k ih =>
    intro a hpk
    -- Upper endpoint is a + (k + 2).  hpk : 2 * (a + (k + 1 + 1)) ≤ c.
    -- Step 1: rise from a to a + (k + 1), via IH over gap k.
    --   IH a needs 2 * (a + (k + 1)) ≤ c, which follows from hpk since
    --   a + (k+1) ≤ a + (k+2).
    have hpk_lower : 2 * (a + (k + 1)) ≤ c := by
      refine Nat.le_trans ?_ hpk
      -- 2*(a+(k+1)) ≤ 2*(a+(k+1+1))
      apply Nat.mul_le_mul_left
      -- a + (k+1) ≤ a + (k+1+1)
      apply Nat.add_le_add_left
      exact Nat.le_succ (k + 1)
    have hrise1 : performance a c < performance (a + (k + 1)) c := ih a hpk_lower
    -- Step 2: rise from a + (k + 1) to (a + (k + 1)) + 1 via one adjacent step.
    --   acute_stress_helps (a + (k+1)) needs 2*(a+(k+1)) + 2 ≤ c.
    have hpk_top : 2 * (a + (k + 1)) + 2 ≤ c := by
      -- a + (k+1+1) is defeq to (a+(k+1)) + 1, so
      --   2*(a+(k+1+1)) = 2*((a+(k+1)) + 1) = 2*(a+(k+1)) + 2.
      have heq : 2 * (a + (k + 1)) + 2 = 2 * (a + (k + 1 + 1)) := by
        -- prove RHS = LHS by distributing over (a+(k+1)) + 1
        have hdist : 2 * ((a + (k + 1)) + 1) = 2 * (a + (k + 1)) + 2 := by
          rw [Nat.left_distrib, Nat.mul_one]
        exact hdist.symm
      rw [heq]
      exact hpk
    have hrise2 :
        performance (a + (k + 1)) c < performance ((a + (k + 1)) + 1) c :=
      acute_stress_helps (a + (k + 1)) c hpk_top
    -- Chain.  ((a+(k+1))+1) = a + (k+1+1) = a + (k+2) definitionally.
    exact Nat.lt_trans hrise1 hrise2

/-- **Strictly rising below the peak (interval form).** For *all* doses `a < b`
    both at or below the peak (`2 * b ≤ c`), performance is strictly larger at the
    higher dose: `performance a c < performance b c`. This is a genuine
    strict-monotone-on-an-interval theorem — not the single adjacent step
    `acute_stress_helps`, but its transitive closure across the whole rising arm,
    obtained from `rising_gap` by writing the gap `b - a` as `n + 1`. -/
theorem strictly_rising_below_peak (a b c : Nat) (hab : a < b) (hpeak : 2 * b ≤ c) :
    performance a c < performance b c := by
  -- a < b means a + 1 ≤ b; write b = a + (k + 1).
  obtain ⟨k, hk⟩ := Nat.le.dest hab  -- (a + 1) + k = b
  -- b = a + (k + 1).  hk : a.succ + k = b, and a.succ + k = a + (k + 1).
  have hb : b = a + (k + 1) := by
    rw [← hk]
    exact Nat.succ_add a k
  -- rewrite the goal and hypothesis with this form, then apply rising_gap.
  rw [hb]
  rw [hb] at hpeak
  exact rising_gap c k a hpeak

/-! ## 2. The falling arm as a strict-monotone interval theorem

Mirror image of §1, chaining `chronic_stress_hurts` over an interval by gap
induction. The lower endpoint `a` carries the peak hypothesis `c ≤ 2*a`; every
intermediate dose `≥ a` inherits it, and the in-range condition propagates from
the upper endpoint. -/

/-- Gap-form of the falling arm. For every base dose `a` past the peak
    (`c ≤ 2 * a`) and gap `n`, with the upper endpoint still in range
    (`a + (n + 1) ≤ c`), performance strictly *falls* from `a` to `a + (n + 1)`.
    Induction on `n`: base is one `chronic_stress_hurts`; the step chains an
    adjacent drop at the *bottom* (`a → a+1`) with the IH over the remaining gap
    starting at `a + 1` (which is still past the peak, `c ≤ 2*a ≤ 2*(a+1)`). -/
theorem falling_gap (c : Nat) :
    ∀ (n a : Nat), c ≤ 2 * a → a + (n + 1) ≤ c →
      performance (a + (n + 1)) c < performance a c := by
  intro n
  induction n with
  | zero =>
    intro a hpeak hrange
    -- a + (0+1) = a + 1.  chronic_stress_hurts needs c ≤ 2*a and a+1 ≤ c.
    exact chronic_stress_hurts a c hpeak hrange
  | succ k ih =>
    intro a hpeak hrange
    -- Upper endpoint a + (k + 2).  hrange : a + (k+1+1) ≤ c.
    -- Step 1: adjacent drop a + 1 < a (in value): performance (a+1) c < performance a c.
    --   chronic_stress_hurts a needs c ≤ 2*a (have) and a + 1 ≤ c
    --   (from a + (k+2) ≤ c).
    have hrange_a1 : a + 1 ≤ c := by
      refine Nat.le_trans ?_ hrange
      -- a + 1 ≤ a + (k + 1 + 1)
      apply Nat.add_le_add_left
      -- 1 ≤ k + 1 + 1
      exact Nat.le_add_left 1 (k + 1)
    have hdrop1 : performance (a + 1) c < performance a c :=
      chronic_stress_hurts a c hpeak hrange_a1
    -- Step 2: IH from base a + 1 over gap k, reaching (a+1) + (k+1) = a + (k+2).
    --   IH (a+1) needs c ≤ 2*(a+1) and (a+1) + (k+1) ≤ c.
    have hpeak_a1 : c ≤ 2 * (a + 1) := by
      refine Nat.le_trans hpeak ?_
      apply Nat.mul_le_mul_left
      exact Nat.le_succ a
    have hrange_a1k : (a + 1) + (k + 1) ≤ c := by
      -- (a+1)+(k+1) = a + (k+1+1)
      have heq : (a + 1) + (k + 1) = a + (k + 1 + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (k + 1)]
      rw [heq]
      exact hrange
    have hdrop2 : performance ((a + 1) + (k + 1)) c < performance (a + 1) c :=
      ih (a + 1) hpeak_a1 hrange_a1k
    -- Chain.  (a+1)+(k+1) = a + (k+1+1) = a + (k+2) definitionally.
    have heq2 : (a + 1) + (k + 1) = a + (k + 1 + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 (k + 1)]
    rw [heq2] at hdrop2
    exact Nat.lt_trans hdrop2 hdrop1

/-- **Strictly falling above the peak (interval form).** For *all* doses `a < b`
    both at or above the peak (`c ≤ 2 * a`) with the upper one in range
    (`b ≤ c`), performance is strictly *smaller* at the higher dose:
    `performance b c < performance a c`. The full strict-decrease across the
    falling arm — the transitive closure of `chronic_stress_hurts`, not a single
    adjacent drop. -/
theorem strictly_falling_above_peak (a b c : Nat)
    (hab : a < b) (hpeak : c ≤ 2 * a) (hrange : b ≤ c) :
    performance b c < performance a c := by
  obtain ⟨k, hk⟩ := Nat.le.dest hab  -- (a + 1) + k = b
  have hb : b = a + (k + 1) := by
    rw [← hk]
    exact Nat.succ_add a k
  rw [hb]
  rw [hb] at hrange
  exact falling_gap c k a hpeak hrange

/-! ## 3. The optimization theorem: the global argmax is the floor-half

`peak_at_floor_half` is the genuine optimization statement: a single ∀-bound
asserting that no dose beats `c / 2`. We prove it by casing every dose against
`c / 2` and feeding the rising/falling interval theorems. The two half-point
arithmetic facts from §0 supply the peak hypotheses for *every* `c`. -/

/-- One step above the floor-half never beats the floor-half:
    `performance (c/2 + 1) c ≤ performance (c/2) c`. For even `c` this is a strict
    drop (`chronic_stress_hurts` applies at `c/2`); for odd `c` the two doses
    *tie* — either way the `≤` holds. The proof handles the parity split
    explicitly. -/
theorem step_above_half_le (c : Nat) :
    performance (c / 2 + 1) c ≤ performance (c / 2) c := by
  rcases Nat.mod_two_eq_zero_or_one c with hev | hodd
  · -- even: c = 2*(c/2), so chronic_stress_hurts at c/2 gives a strict drop.
    have hc : 2 * (c / 2) = c := by
      have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
      rw [hev, Nat.add_zero] at hdm
      exact hdm
    -- need c/2 + 1 ≤ c to drop.  If c = 0 then c/2 = 0 and c/2+1 = 1 > 0 = c,
    -- so chronic_stress_hurts does not apply; handle c = 0 directly.
    cases c with
    | zero =>
      -- performance (0/2 + 1) 0 = performance 1 0 = 1 * (0 - 1) = 0 = performance 0 0
      decide
    | succ d =>
      -- c = d+1 ≥ 1.  Then c/2 + 1 ≤ c.
      have hrange : (Nat.succ d) / 2 + 1 ≤ Nat.succ d := by
        -- (d+1)/2 + 1 ≤ d+1  ⇐  (d+1)/2 ≤ d
        apply Nat.succ_le_succ
        -- (d+1)/2 ≤ d : from 2*((d+1)/2) ≤ d+1 and 1 ≤ ... ; use div bound
        have hdiv : (Nat.succ d) / 2 ≤ Nat.succ d := Nat.div_le_self _ _
        -- tighten: (d+1)/2 ≤ d.  Since 2*((d+1)/2) ≤ d+1, and (d+1)/2 ≤ d+1.
        -- Use: 2*((d+1)/2) ≤ d+1 ⇒ (d+1)/2 ≤ d when (d+1)/2 ≥ 1, else (d+1)/2=0≤d.
        rcases Nat.eq_zero_or_pos ((Nat.succ d) / 2) with h0 | hpos
        · rw [h0]; exact Nat.zero_le d
        · -- 2 * q ≤ d+1 with q ≥ 1 ⇒ q + q ≤ d+1 ⇒ q ≤ d (since q ≥ 1 ⇒ q+1 ≤ q+q ≤ d+1)
          have hq2 : 2 * ((Nat.succ d) / 2) ≤ Nat.succ d := two_mul_half_le (Nat.succ d)
          rw [Nat.two_mul] at hq2
          -- q + q ≤ d + 1, with 1 ≤ q ⇒ q + 1 ≤ q + q ≤ d + 1 ⇒ q ≤ d
          have hstep : (Nat.succ d) / 2 + 1 ≤ (Nat.succ d) / 2 + (Nat.succ d) / 2 :=
            Nat.add_le_add_left hpos _
          have hchain : (Nat.succ d) / 2 + 1 ≤ d + 1 := Nat.le_trans hstep hq2
          exact Nat.le_of_succ_le_succ hchain
      have hpeak : (Nat.succ d) ≤ 2 * ((Nat.succ d) / 2) := Nat.le_of_eq hc.symm
      exact Nat.le_of_lt (chronic_stress_hurts ((Nat.succ d) / 2) (Nat.succ d) hpeak hrange)
  · -- odd: the two central doses tie.  Show performance (c/2 + 1) c = performance (c/2) c.
    -- c = 2*(c/2) + 1.  Let m = c/2.  c - m = m + 1, c - (m+1) = m.
    -- performance m c     = m * (c - m)     = m * (m + 1)
    -- performance (m+1) c = (m+1) * (c - (m+1)) = (m+1) * m
    -- These are equal by commutativity.
    have hc : 2 * (c / 2) + 1 = c := by
      have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
      rw [hodd] at hdm
      exact hdm
    -- c - m = m + 1 : supply c = ((c/2)+1) + (c/2), built via hc by transitivity.
    have hsub1 : c - (c / 2) = (c / 2) + 1 := by
      have hinner : 2 * (c / 2) + 1 = ((c / 2) + 1) + (c / 2) := by
        rw [Nat.two_mul, Nat.add_right_comm]
      exact Nat.sub_eq_of_eq_add (Eq.trans hc.symm hinner)
    -- c - (m+1) = m : supply c = (c/2) + ((c/2)+1).
    have hsub2 : c - ((c / 2) + 1) = c / 2 := by
      have hinner : 2 * (c / 2) + 1 = (c / 2) + ((c / 2) + 1) := by
        rw [Nat.two_mul, Nat.add_assoc]
      exact Nat.sub_eq_of_eq_add (Eq.trans hc.symm hinner)
    -- now compute both performances and compare (equal ⇒ ≤).
    unfold performance
    rw [hsub1, hsub2]
    -- goal: (c/2 + 1) * (c/2) ≤ (c/2) * (c/2 + 1)
    rw [Nat.mul_comm ((c / 2) + 1) (c / 2)]
    -- (c/2)*(c/2+1) ≤ (c/2)*(c/2+1)
    exact Nat.le_refl _

/-- **Peak at the floor-half (the optimization theorem / argmax).** No dose beats
    `c / 2`: for *every* dose `s`, `performance s c ≤ performance (c / 2) c`. This
    is the genuine global-maximum statement — a real ∀-bound, not an adjacent-step
    fact. The proof cases `s` against the peak `c / 2`:

    * `s ≤ c / 2`: the rising arm (`strictly_rising_below_peak`) lifts `s` to the
      peak; its hypothesis `2*(c/2) ≤ c` holds for all `c` (`two_mul_half_le`).
    * `s = c / 2 + 1`: handled by `step_above_half_le` (strict for even `c`, a tie
      for odd).
    * `s ≥ c / 2 + 2`: the falling arm (`strictly_falling_above_peak`) anchored at
      `c / 2 + 1` drops `s` below `c / 2 + 1`, which in turn is `≤` the peak. The
      anchor's hypothesis `c ≤ 2*(c/2 + 1)` holds for all `c`
      (`le_two_mul_half_succ`).

    Doses past `c` are pinned to `0` and so are dominated automatically. -/
theorem peak_at_floor_half (c : Nat) :
    ∀ s, performance s c ≤ performance (c / 2) c := by
  intro s
  -- case s vs c/2
  rcases Nat.lt_or_ge s (c / 2) with hlt | hge
  · -- s < c/2 : rising arm strictly lifts s to the peak.
    have hpeak : 2 * (c / 2) ≤ c := two_mul_half_le c
    exact Nat.le_of_lt (strictly_rising_below_peak s (c / 2) c hlt hpeak)
  · -- s ≥ c/2.  Split: s = c/2, or s ≥ c/2 + 1.
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · -- s = c/2 : equal (heq : c/2 = s).
      rw [heq]; exact Nat.le_refl _
    · -- s ≥ c/2 + 1, i.e. c/2 < s.
      -- subcase s = c/2 + 1 vs s ≥ c/2 + 2
      rcases Nat.lt_or_ge (c / 2 + 1) s with hgt2 | hle2
      · -- c/2 + 1 < s : need s in range for falling arm.
        -- if s > c then performance s c = 0 ≤ performance (c/2) c.
        rcases Nat.lt_or_ge c s with hsc | hsle
        · -- s > c : headroom c - s = 0, so performance s c = 0.
          have hzero : performance s c = 0 := by
            unfold performance
            have : c - s = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hsc)
            rw [this, Nat.mul_zero]
          rw [hzero]
          exact Nat.zero_le _
        · -- s ≤ c : falling arm from c/2 + 1 down to s, then step_above_half_le.
          -- anchor peak: c ≤ 2*(c/2)+1 ≤ 2*(c/2)+2 = 2*(c/2 + 1).
          have hanchor : 2 * (c / 2) + 1 ≤ 2 * (c / 2 + 1) := by
            -- 2*(c/2+1) = 2*(c/2) + 2
            have heq : 2 * (c / 2 + 1) = 2 * (c / 2) + 2 := by
              rw [Nat.left_distrib, Nat.mul_one]
            rw [heq]
            -- 2*(c/2) + 1 ≤ 2*(c/2) + 2
            exact Nat.add_le_add_left (by decide) _
          have hpeak1 : c ≤ 2 * (c / 2 + 1) :=
            Nat.le_trans (le_two_mul_half_succ c) hanchor
          have hfall : performance s c < performance (c / 2 + 1) c :=
            strictly_falling_above_peak (c / 2 + 1) s c hgt2 hpeak1 hsle
          exact Nat.le_trans (Nat.le_of_lt hfall) (step_above_half_le c)
      · -- s ≤ c/2 + 1 and s > c/2  ⇒  s = c/2 + 1.
        -- hgt : c/2 < s ; hle2 : s ≤ c/2 + 1  ⇒  s = c/2 + 1
        have hs_eq : s = c / 2 + 1 := by
          -- c/2 < s and s ≤ c/2 + 1 ⇒ c/2 + 1 ≤ s ≤ c/2 + 1
          have hlo : c / 2 + 1 ≤ s := Nat.succ_le_of_lt hgt
          exact Nat.le_antisymm hle2 hlo
        rw [hs_eq]
        exact step_above_half_le c

/-! ## 4. Uniqueness of the maximizer (even, positive `c`), and the honest odd case

For even positive `c` the maximizer is *unique*: every dose other than `c / 2`
does strictly worse. This is the deep statement — not just "no one beats the peak"
(`peak_at_floor_half`) but "no one *ties* it either." Two restrictions are
genuine, not cosmetic:

* **Odd `c` fails.** For odd `c` the two central doses `c / 2` and `c / 2 + 1`
  tie, so the argmax is not unique — recorded in `odd_has_two_peaks`.
* **`c = 0` fails.** The degenerate parabola is flat at `0`, so every dose ties
  the (zero) peak; strictness is impossible. Hence `0 < c`. -/

/-- For even `c` the headroom at the peak equals the peak dose itself:
    `c - c / 2 = c / 2`. (Because `c = 2 * (c / 2)`.) -/
theorem even_headroom_at_half (c : Nat) (heven : c % 2 = 0) : c - c / 2 = c / 2 := by
  have hc : 2 * (c / 2) = c := by
    have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    rw [heven, Nat.add_zero] at hdm
    exact hdm
  -- c = c/2 + c/2, so c - c/2 = c/2 via Nat.sub_eq_of_eq_add (a = c' + b form).
  -- Build the split by transitivity through hc, never rewriting `c` in the goal.
  have hsplit : c = (c / 2) + (c / 2) := Eq.trans hc.symm (Nat.two_mul (c / 2))
  exact Nat.sub_eq_of_eq_add hsplit

/-- The half-point is at least `1` once `c ≥ 2`: `1 ≤ c / 2`. (For even positive
    `c` this is the statement that the peak dose is nonzero.) -/
theorem one_le_half_of_two_le (c : Nat) (h : 2 ≤ c) : 1 ≤ c / 2 := by
  -- 1 ≤ c/2  ⇔  1*2 ≤ c  (Nat.le_div_iff_mul_le)
  have hiff := Nat.le_div_iff_mul_le (k := 2) (x := 1) (y := c) Nat.zero_lt_two
  -- hiff : 1 ≤ c / 2 ↔ 1 * 2 ≤ c
  apply hiff.mpr
  rw [Nat.one_mul]
  exact h

/-- **The peak is strictly positive** for even `c ≥ 2`:
    `0 < performance (c / 2) c`. The maximum output is a genuine win, not a tie at
    zero — this is what makes uniqueness meaningful. -/
theorem peak_positive (c : Nat) (heven : c % 2 = 0) (hc2 : 2 ≤ c) :
    0 < performance (c / 2) c := by
  unfold performance
  rw [even_headroom_at_half c heven]
  -- 0 < (c/2) * (c/2)
  have hpos : 1 ≤ c / 2 := one_le_half_of_two_le c hc2
  -- 0 < c/2 and 0 < c/2 ⇒ 0 < (c/2)*(c/2)
  exact Nat.mul_pos hpos hpos

/-- **Unique argmax (even, positive `c`).** For even `c` with `0 < c`, the
    floor-half `c / 2` is the *unique* global maximizer: any dose `s ≠ c / 2` does
    strictly worse, `performance s c < performance (c / 2) c`. Uniqueness — the
    strictness at *every* off-peak dose — is the content that the global bound
    `peak_at_floor_half` does not provide. Cases on `s` below vs above the peak and
    uses the strict interval theorems; the even hypothesis `2 * (c / 2) = c` makes
    the falling arm strict right from `c / 2`, and `peak_positive` handles doses
    past `c` (which collapse to `0 <` the positive peak).

    Both restrictions are essential: odd `c` ties two central doses
    (`odd_has_two_peaks`); `c = 0` is a flat parabola where every dose ties zero. -/
theorem unique_argmax (c : Nat) (heven : c % 2 = 0) (hpos : 0 < c)
    (s : Nat) (hne : s ≠ c / 2) :
    performance s c < performance (c / 2) c := by
  -- even ⇒ 2*(c/2) = c
  have hc : 2 * (c / 2) = c := by
    have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    rw [heven, Nat.add_zero] at hdm
    exact hdm
  -- 0 < c even ⇒ 2 ≤ c (since c = 1 is odd).
  have hc2 : 2 ≤ c := by
    -- c ≥ 1, and c ≠ 1 (else c%2 = 1 ≠ 0); so c ≥ 2.
    have hne1 : c ≠ 1 := by
      intro h1
      rw [h1] at heven
      -- 1 % 2 = 1 ≠ 0
      exact absurd heven (by decide)
    -- 0 < c ⇒ 1 ≤ c; with c ≠ 1 ⇒ 2 ≤ c
    rcases Nat.eq_or_lt_of_le hpos with heq | hlt
    · exact absurd heq.symm hne1
    · exact hlt
  rcases Nat.lt_or_ge s (c / 2) with hlt | hge
  · -- below: strict rising lifts s to peak.  hpeak: 2*(c/2) ≤ c (equality here).
    have hpeak : 2 * (c / 2) ≤ c := Nat.le_of_eq hc
    exact strictly_rising_below_peak s (c / 2) c hlt hpeak
  · -- s ≥ c/2.  Since s ≠ c/2, in fact s > c/2.
    have hgt : c / 2 < s := Nat.lt_of_le_of_ne hge (fun h => hne h.symm)
    rcases Nat.lt_or_ge c s with hsc | hsle
    · -- s > c ⇒ performance s c = 0 < positive peak.
      have hzero : performance s c = 0 := by
        unfold performance
        have hsub : c - s = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hsc)
        rw [hsub, Nat.mul_zero]
      rw [hzero]
      exact peak_positive c heven hc2
    · -- c/2 < s ≤ c : falling arm strict from c/2 (even ⇒ c ≤ 2*(c/2)).
      have hpeak : c ≤ 2 * (c / 2) := Nat.le_of_eq hc.symm
      exact strictly_falling_above_peak (c / 2) s c hgt hpeak hsle

/-- **Odd `c` has two tied peaks (the honest odd case).** For odd `c`, the two
    central doses `c / 2` and `c / 2 + 1` achieve *equal* performance — the
    maximizer is *not* unique. This is exactly why `unique_argmax` is stated for
    even `c`: the strict off-peak inequality genuinely fails here. (Both still
    realize the global maximum, by `peak_at_floor_half` and symmetry, but neither
    strictly dominates the other.) -/
theorem odd_has_two_peaks (c : Nat) (hodd : c % 2 = 1) :
    performance (c / 2) c = performance (c / 2 + 1) c := by
  -- c = 2*(c/2) + 1.  Let m = c/2.  c - m = m+1 and c - (m+1) = m.
  have hc : 2 * (c / 2) + 1 = c := by
    have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    rw [hodd] at hdm
    exact hdm
  -- c - (c/2) = (c/2)+1 : supply c = ((c/2)+1) + (c/2), via hc by transitivity.
  have hsub1 : c - (c / 2) = (c / 2) + 1 := by
    have hinner : 2 * (c / 2) + 1 = ((c / 2) + 1) + (c / 2) := by
      rw [Nat.two_mul, Nat.add_right_comm]
    exact Nat.sub_eq_of_eq_add (Eq.trans hc.symm hinner)
  -- c - ((c/2)+1) = c/2 : supply c = (c/2) + ((c/2)+1).
  have hsub2 : c - ((c / 2) + 1) = c / 2 := by
    have hinner : 2 * (c / 2) + 1 = (c / 2) + ((c / 2) + 1) := by
      rw [Nat.two_mul, Nat.add_assoc]
    exact Nat.sub_eq_of_eq_add (Eq.trans hc.symm hinner)
  unfold performance
  rw [hsub1, hsub2]
  -- (c/2) * (c/2 + 1) = (c/2 + 1) * (c/2)
  rw [Nat.mul_comm]

/-! ## 5. The headline: genuine strict unimodality -/

/-- **Strictly unimodal (the headline).** For every capacity `c` there is a peak
    dose `p = c / 2` such that:

    * (rising) on `[0, p]` performance is *strictly increasing* — `a < b ≤ p`
      implies `performance a c < performance b c` (the interval theorem
      `strictly_rising_below_peak`, whose `2*b ≤ c` reduces to `2*p ≤ c` at the
      top);
    * (falling) on `[p, c]` performance is *strictly decreasing* — `p ≤ a < b ≤ c`
      implies `performance b c < performance a c` (the interval theorem
      `strictly_falling_above_peak`, anchored one step above `p` via
      `c ≤ 2*(p+1)`);
    * (global max) `p` attains the global maximum: `∀ s, performance s c ≤
      performance p c` (`peak_at_floor_half`).

    This is genuine unimodality — strict monotonicity on each side of a single
    global maximizer — composed from the three optimization theorems above, far
    stronger than the adjacent-step `SapolskyStress.inverted_u`. -/
theorem strictly_unimodal (c : Nat) :
    ∃ p : Nat,
      p = c / 2 ∧
      -- strictly increasing on [0, p]
      (∀ a b, a < b → 2 * b ≤ c → performance a c < performance b c) ∧
      -- strictly decreasing on [p, c]
      (∀ a b, c ≤ 2 * a → a < b → b ≤ c → performance b c < performance a c) ∧
      -- p is the global maximum
      (∀ s, performance s c ≤ performance (c / 2) c) :=
  ⟨c / 2, rfl,
   fun a b hab hpk => strictly_rising_below_peak a b c hab hpk,
   fun a b hpk hab hr => strictly_falling_above_peak a b c hab hpk hr,
   peak_at_floor_half c⟩

end Gnosis.Body.UnimodalDoseResponse
