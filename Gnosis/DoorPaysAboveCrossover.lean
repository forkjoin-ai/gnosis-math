import Init

/-
  DoorPaysAboveCrossover.lean
  ===========================

  Yet-unfolded wisdom from a measured failure.

  We ran the FOIL value-fingerprint cache against cold recompute on cheap work
  (26 ns Fibonacci) and it was a SLOWDOWN — 0.71–0.96×, "NOT EARNED". The runtime
  was right to gate it off (the Reynolds crossover). The failure is the lesson:

    The value-door (`ValueIsTheDoor`) is always SOUND — checking the Value is the
    correct way to eliminate falsehood. But it is only FAST when the work it
    eliminates exceeds the cost of the gate itself. Soundness is not speed.

  Model (per a batch of `N` queries): without the gate, pay recompute `r` on each
  hit-able query; with the gate, pay the gate `g` on every query, still recompute
  `r` on the `N - h` misses, plus one-time `setup`. Net work saved:

      netSaved = h·r  −  (N·g + setup)

  and it is positive exactly when the eliminated recompute `h·r` beats the gate
  cost. The crossover is `r` vs `g` — recompute cost vs discriminator cost. THAT
  GAP IS THE VERIFY-VS-SEARCH GAP: the door pays in proportion to how much harder
  finding is than checking. For cheap work (`r ≤ g`) it never pays (the measured
  failure); for NP-shaped work (`r` super-polynomial, `g` cheap) it pays
  enormously. P vs NP is precisely the question of whether that gap is real.

  Init only. Zero `sorry`, zero new `axiom`.
-/

namespace DoorPaysAboveCrossover

/-- Net work saved by the value-gate over a batch: `h` hits each eliminate
    recompute `r`; every one of `N` queries pays the gate `g`; plus one-time
    `setup`. (Signed: a loss is negative.) -/
def netSaved (N h r g setup : Nat) : Int := (h * r : Int) - (N * g + setup)

/-- **The door pays iff it eliminates more than it costs.** Net benefit is
    positive exactly when the recompute saved on hits (`h·r`) exceeds the total
    gate cost (`N·g + setup`). -/
theorem door_pays_iff (N h r g setup : Nat) :
    0 < netSaved N h r g setup ↔ N * g + setup < h * r := by
  unfold netSaved
  constructor
  · intro h; omega
  · intro h; omega

/-- **The measured failure, as law: cheap recompute never pays.** If a single
    recompute is no costlier than the gate (`r ≤ g`), the value-door is a net loss
    no matter the hit rate — exactly what the 26 ns FOIL benchmark showed
    (0.71–0.96×, NOT EARNED). The door costs more than the room behind it. -/
theorem cheap_recompute_no_benefit (N h r g setup : Nat) (hr : r ≤ g) (hh : h ≤ N) :
    netSaved N h r g setup ≤ 0 := by
  have hle : h * r ≤ N * g := Nat.mul_le_mul hh hr
  unfold netSaved
  omega

/-- **The door pays above the crossover.** When the gate cost is paid down by the
    eliminated recompute, the benefit is real — the complement of the failure. -/
theorem expensive_recompute_pays (N h r g setup : Nat)
    (hgap : N * g + setup < h * r) : 0 < netSaved N h r g setup :=
  (door_pays_iff N h r g setup).mpr hgap

/-- **The crossover is the verify-vs-search gap.** Restated at one query with one
    hit (`N = 1, h = 1, setup = 0`): the value-door wins iff recompute `r` strictly
    exceeds the gate `g` — iff finding the answer the slow way costs more than
    checking the Value. The door's speedup IS the verify-search separation; for NP
    that gap is the whole point, for 26 ns work it is nothing. -/
theorem crossover_is_verify_search_gap (r g : Nat) :
    0 < netSaved 1 1 r g 0 ↔ g < r := by
  unfold netSaved
  constructor
  · intro h; omega
  · intro h; omega

end DoorPaysAboveCrossover
