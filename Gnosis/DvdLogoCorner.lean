import Init

/-!
# DvdLogoCorner — does the bouncing DVD logo ever hit a corner?

The screensaver logo moves diagonally and reflects off the walls of a `W × H` box. By the
standard billiard *unfolding*, the diagonal bounce is a straight line on a torus, and the
two coordinates decouple into independent triangle waves. The logo touches a *vertical* wall
exactly when `(x0 + t) ≡ 0 (mod W)` and a *horizontal* wall when `(y0 + t) ≡ 0 (mod H)`; a
**corner** is both at once. So the whole question is the single predicate

```
cornerHit W H x0 y0 t  :=  (x0 + t) % W = 0  ∧  (y0 + t) % H = 0.
```

This is the conservative / periodic regime of `Gnosis/FiniteDynamicsCore.lean`: the
corner-phase is a *conserved observable* across the period `W * H`
(`cornerHit_add_mul` — the screensaver analogue of `returns_conserves`). The payoff of
finiteness: an honestly *infinite-time* question — "does it EVER get stuck in a corner?" —
becomes **decidable**, because the pattern repeats every `W * H` ticks, so checking one
period settles all of time (`everHits_iff`).

Number theory says the logo eventually hits a corner iff `x0 ≡ y0 (mod gcd W H)` (Chinese
Remainder Theorem). We do not prove that `iff` here — CRT solvability needs Bézout, heavy in
Init-only — but the periodicity reduction makes every concrete box `decide`-able, which is
the constructive answer. Coprime dimensions (`gcd = 1`) always hit; a shared factor can trap
the logo forever, as `dvd_4x6_from_0_1_never` certifies.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace DvdLogoCorner

/-- The logo is at a corner at tick `t`: at a vertical wall (`x ≡ 0 mod W`) and a horizontal
    wall (`y ≡ 0 mod H`) simultaneously. Returned as `Bool` so finite checks are `decide`-able. -/
def cornerHit (W H x0 y0 t : Nat) : Bool :=
  ((x0 + t) % W == 0) && ((y0 + t) % H == 0)

/-- The logo hits a corner at some (unbounded) future tick. -/
def everHits (W H x0 y0 : Nat) : Prop := ∃ t, cornerHit W H x0 y0 t = true

/-- The corner-phase is conserved across one period `W * H`: adding `W * H` ticks leaves the
    corner predicate unchanged (`W ∣ W*H` and `H ∣ W*H` kill the offsets). -/
theorem cornerHit_period (W H x0 y0 b : Nat) :
    cornerHit W H x0 y0 (b + W * H) = cornerHit W H x0 y0 b := by
  unfold cornerHit
  have hx : (x0 + (b + W * H)) % W = (x0 + b) % W := by
    rw [← Nat.add_assoc]; exact Nat.add_mul_mod_self_left (x0 + b) W H
  have hy : (y0 + (b + W * H)) % H = (y0 + b) % H := by
    rw [← Nat.add_assoc]; exact Nat.add_mul_mod_self_right (y0 + b) W H
  rw [hx, hy]

/-- Conserved across every whole number of periods: the corner-phase observable returns. -/
theorem cornerHit_add_mul (W H x0 y0 a k : Nat) :
    cornerHit W H x0 y0 (a + W * H * k) = cornerHit W H x0 y0 a := by
  induction k with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, cornerHit_period, ih]

/-- Folding a tick into its residue mod `W * H` does not change whether it is a corner. -/
theorem cornerHit_mod (W H x0 y0 t : Nat) :
    cornerHit W H x0 y0 (t % (W * H)) = cornerHit W H x0 y0 t := by
  have h := cornerHit_add_mul W H x0 y0 (t % (W * H)) (t / (W * H))
  rw [Nat.mod_add_div t (W * H)] at h
  exact h.symm

/-- **Decidability of an infinite question.** Because the corner pattern is periodic, the
    logo hits a corner at *some* time iff it does so within the first `W * H` ticks. This
    reduces an unbounded `∃` over all of time to a bounded, `decide`-able window. -/
theorem everHits_iff (W H x0 y0 : Nat) (hpos : 0 < W * H) :
    everHits W H x0 y0 ↔ ∃ t, t < W * H ∧ cornerHit W H x0 y0 t = true := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t % (W * H), Nat.mod_lt t hpos, by rw [cornerHit_mod]; exact ht⟩
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩

-- ═══════════════════════════════════════════════════════════════════════
-- Concrete verdicts (each settled for all time by checking one period)
-- ═══════════════════════════════════════════════════════════════════════

/-- A 4×6 box started at (0,1): gcd(4,6)=2 and 0 ≢ 1 (mod 2), so the logo is trapped — it
    never reaches a corner, certified across the whole 24-tick period. -/
theorem dvd_4x6_from_0_1_never : ¬ everHits 4 6 0 1 := by
  rw [everHits_iff 4 6 0 1 (by decide)]
  rintro ⟨t, hlt, hhit⟩
  have hfalse : cornerHit 4 6 0 1 t = false := by
    have hcheck : ∀ s, s < 4 * 6 → cornerHit 4 6 0 1 s = false := by decide
    exact hcheck t hlt
  rw [hfalse] at hhit
  exact Bool.noConfusion hhit

/-- A 6×9 box started at (1,2): gcd(6,9)=3 and 1 ≢ 2 (mod 3), trapped forever. -/
theorem dvd_6x9_from_1_2_never : ¬ everHits 6 9 1 2 := by
  rw [everHits_iff 6 9 1 2 (by decide)]
  rintro ⟨t, hlt, hhit⟩
  have hfalse : cornerHit 6 9 1 2 t = false := by
    have hcheck : ∀ s, s < 6 * 9 → cornerHit 6 9 1 2 s = false := by decide
    exact hcheck t hlt
  rw [hfalse] at hhit
  exact Bool.noConfusion hhit

/-- A 4×6 box started at (1,3): 1 ≡ 3 (mod 2), so it does hit — at tick 3. -/
theorem dvd_4x6_from_1_3_hits : everHits 4 6 1 3 := ⟨3, by decide⟩

/-- A 5×3 box (coprime, gcd 1) started at (0,1): coprime dimensions always hit; here at tick 5. -/
theorem dvd_5x3_from_0_1_hits : everHits 5 3 0 1 := ⟨5, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- The trap FORMULA — infinitely many "stuck forever" boxes, in one stroke
-- ═══════════════════════════════════════════════════════════════════════

/-- If two numbers are each the *same* amount `t` above a multiple of `g`, they share a
    residue mod `g`. This is the easy, Bézout-free half of the Chinese Remainder criterion. -/
theorem mod_eq_of_dvd_add (g x y t : Nat)
    (hx : g ∣ (x + t)) (hy : g ∣ (y + t)) : x % g = y % g := by
  obtain ⟨m, hm⟩ := hx          -- x + t = g * m
  obtain ⟨n, hn⟩ := hy          -- y + t = g * n
  -- both sides equal x + y + t, so x + g*n = y + g*m
  have key : x + g * n = y + g * m := by rw [← hn, ← hm, Nat.add_left_comm]
  have h2 : (x + g * n) % g = (y + g * m) % g := by rw [key]
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h2

/-- **THE TRAP FORMULA.** Pick any common factor `g` of the box (`g ∣ W`, `g ∣ H`). If the
    start offsets fall in *different* residue classes mod `g` (`x0 % g ≠ y0 % g`), the logo is
    stuck forever — it never reaches a corner. One theorem, infinitely many boxes. The proof
    is the Init-only direction of the CRT criterion: a corner forces `g ∣ (x0+t)` and
    `g ∣ (y0+t)`, hence `x0 ≡ y0 (mod g)`, contradicting the hypothesis. (The converse —
    `x0 ≡ y0 (mod gcd)` ⇒ it hits — needs Bézout and is deliberately out of scope here.) -/
theorem trapped_of_common_divisor (W H x0 y0 g : Nat)
    (hgW : g ∣ W) (hgH : g ∣ H) (hne : x0 % g ≠ y0 % g) :
    ¬ everHits W H x0 y0 := by
  rintro ⟨t, ht⟩
  unfold cornerHit at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  exact hne (mod_eq_of_dvd_add g x0 y0 t
    (Nat.dvd_trans hgW (Nat.dvd_of_mod_eq_zero ht.1))
    (Nat.dvd_trans hgH (Nat.dvd_of_mod_eq_zero ht.2)))

/-- Infinite family #1 (parity trap): every box with **both sides even**, started at an
    even/odd offset like `(0,1)`, is stuck forever — `g = 2` always separates the residues. -/
theorem trapped_even_box (a b : Nat) : ¬ everHits (2 * a) (2 * b) 0 1 :=
  trapped_of_common_divisor (2 * a) (2 * b) 0 1 2 ⟨a, rfl⟩ ⟨b, rfl⟩ (by decide)

/-- Infinite family #2 (mod-3 trap): every `3a × 3b` box started at `(0,1)` is stuck forever. -/
theorem trapped_triple_box (a b : Nat) : ¬ everHits (3 * a) (3 * b) 0 1 :=
  trapped_of_common_divisor (3 * a) (3 * b) 0 1 3 ⟨a, rfl⟩ ⟨b, rfl⟩ (by decide)

/-- Infinite family #3 (general `g`): for **every** `g ≥ 2`, the `g·a × g·b` box started at
    `(0,1)` is stuck forever — `0` and `1` are distinct residues once `g ≥ 2`. A single
    formula whose instances are all the scaled boxes. -/
theorem trapped_scaled_box (g a b : Nat) (hg : 2 ≤ g) :
    ¬ everHits (g * a) (g * b) 0 1 :=
  trapped_of_common_divisor (g * a) (g * b) 0 1 g ⟨a, rfl⟩ ⟨b, rfl⟩ (by
    have h1 : (1 : Nat) < g := Nat.lt_of_lt_of_le (by decide) hg
    rw [Nat.zero_mod, Nat.mod_eq_of_lt h1]; decide)

/--
Master verdict. The DVD-corner question is decidable (periodicity); a shared-factor
*formula* (`trapped_of_common_divisor`) certifies infinitely many boxes that trap the logo
forever; and concretely some boxes trap it while others guarantee a corner strike.
-/
theorem dvd_logo_corner_master :
    (∀ W H x0 y0, 0 < W * H →
        (everHits W H x0 y0 ↔ ∃ t, t < W * H ∧ cornerHit W H x0 y0 t = true)) ∧
    (∀ W H x0 y0 g, g ∣ W → g ∣ H → x0 % g ≠ y0 % g → ¬ everHits W H x0 y0) ∧
    (¬ everHits 4 6 0 1) ∧
    (¬ everHits 6 9 1 2) ∧
    everHits 4 6 1 3 ∧
    everHits 5 3 0 1 :=
  ⟨everHits_iff, trapped_of_common_divisor, dvd_4x6_from_0_1_never, dvd_6x9_from_1_2_never,
    dvd_4x6_from_1_3_hits, dvd_5x3_from_0_1_hits⟩

end DvdLogoCorner
end Gnosis
