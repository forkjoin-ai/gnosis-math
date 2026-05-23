import Init
import Gnosis.GnosisTriptychBraid
import Gnosis.SignalNotNoise

/-!
# The Braided Infinite Tower — The Wave Folds Into a Braid, and the Braid Recurs Forever

**THESIS.** The standing wave folds into a **braid**. The fold is not a single
crossing but a *cycle of crossings* — strands passing over and under, returning to
where they began only after three. That braid is the `{−1, 0, +1}` triptych of
`Gnosis.GnosisTriptychBraid`: the wave's fold cycles `failure → truth → wisdom →
failure` with **period 3** (the strands cross three times, then close). And that
braid does not happen once. It recurs at **every level of an infinite tower** —
self-similar, never terminating, always another braid at higher resolution. This
is the structural keystone under **SurfTheory** (`Gnosis.TheWave`,
`Gnosis.ThePipe`): the **pipe** is precisely *where the wave braids on
itself* — the fold curling over into a closed loop of strands, and that fold
recurring up the tower forever.

Two facts here are real theorems, not restatements:

1. **The period-3 closure.** The braid closes after exactly three crossings,
   returning every strand to itself. This is `Gnosis.GnosisTriptychBraid`'s `k=3`
   cycle, reused and lifted to the tower (`the_fold_is_a_braid`,
   `climbing_returns_the_braid`). It is a genuine recurrence: the strands cross,
   and at the third crossing the loop closes.

2. **The never-terminating tower.** `∀ n, ∃ (n+1)` — for every level there is a
   level above it. The tower has no top. This bridges to
   `Gnosis.SignalNotNoise.always_another_wave` (`∀ n, 1 ≤ residual q n`):
   another wave at higher resolution **is** another braid up the tower. There is
   no noise floor; there is no braid floor (`the_tower_never_terminates`).

## Bridges

- **Imported + opened** `Gnosis.GnosisTriptychBraid` — `failure := -1`,
  `truth := 0`, `wisdom := 1`, `triptychSucc`, `iterateTriptych`, and its
  period-3 step theorems (`three_step_returns`). The wave's fold **is** this
  period-3 braid: the strands `failure → truth → wisdom → failure`. We reuse
  `iterateTriptych` verbatim.
- **Imported + opened** `Gnosis.SignalNotNoise` — "always another wave at
  higher resolution" (`always_another_wave`). The tower never terminating **is**
  that scale-invariance; `the_tower_never_terminates` bridges to it.

## Cited (not imported)

- `Gnosis.BuleyClinamenBraid` — the clinamen woven as a braid.
- `Gnosis.FrfWitnessTower`, `Gnosis.BootstrapTowers` — the infinite-tower form.
- `Gnosis.AeonTwelveBraid` — a higher-order braid catalog entry.
- `Gnosis.UniversalStandingWaveTheorem` — the standing wave whose fold this is.
- `Gnosis.TheWave`, `Gnosis.ThePipe` — SurfTheory; the pipe is where
  the wave braids on itself.

## Restriction (stated honestly)

The period-3 closure `iterateTriptych 3 s = s` does **not** hold for *every*
`Int` `s`: a strand off the triad (say `s = 5`) collapses under one crossing to
`failure = -1` and then cycles `-1 → 0 → 1`, landing on `wisdom = 1 ≠ 5`. So the
honest universal claim is **not** "every integer is period-3" but two precise
facts that *are* fully general:

- **On the braid's strands** (the triad `{−1, 0, +1}`), the closure is exact:
  `iterateTriptych 3 s = s` for `s ∈ {failure, truth, wisdom}`. These *are* the
  braid; the wave folds onto them.
- **After one crossing**, *every* strand is in the triad, so
  `iterateTriptych 3 (cross s) = cross s` holds for **all** `s` (`Int`). Once the
  wave has folded even once, the braid is period-3 forever, from any starting
  strand. This is a genuine `∀ s : Int` theorem, proved structurally
  (`closure_after_crossing`).

The tower is indexed by `Nat`; "infinite" means *no top level* (`∀ n, ∃ above`),
the honest finitary reading of an infinite tower in `Nat`-only style. The
self-similarity (`every_level_is_the_same_braid`) is a real `∀ n` statement that
the braid function at level `n+1` equals the braid function at level `n` — the
same period-3 structure at every scale.

`import Init` + Init-clean siblings only. NO Mathlib. `Nat`/`Int` only, no Float,
no Real. Zero `sorry`, zero new `axiom`. Real `Nat` induction for the tower.
-/

namespace Gnosis.BraidedInfiniteTower

open Gnosis.GnosisTriptychBraid
open Gnosis.SignalNotNoise

/-! ## 0. The braid is the period-3 triptych cycle (reused verbatim)

The wave's fold cycles `failure → truth → wisdom → failure`. The crossing is
`triptychSucc`; iterating it is `iterateTriptych`. We reuse these directly from
`Gnosis.GnosisTriptychBraid` — the braid the wave folds into is *literally* the
triptych braid, no re-encoding. -/

/-- One crossing of the braid: the triptych clinamen `triptychSucc`. A strand
    passes over/under to the next: `failure → truth → wisdom → failure`. -/
def cross (s : Int) : Int := triptychSucc s

theorem cross_is_triptychSucc (s : Int) : cross s = triptychSucc s := rfl

/-- `n` crossings of the braid from strand `s`: `iterateTriptych` reused verbatim.
    The braid *at a given level* is this iterated crossing — and (THM 2) the
    function is the same at every level of the tower (self-similar). The `level`
    binder is deliberately *not used* in the body: that is the formal content of
    scale-invariance — the braid is identical at every level, so
    `every_level_is_the_same_braid` holds by `rfl`. -/
def braidAt (_level : Nat) (n : Nat) (s : Int) : Int := iterateTriptych n s

theorem braidAt_is_iterate (level n : Nat) (s : Int) :
    braidAt level n s = iterateTriptych n s := rfl

/-- A level index in the tower. The tower's `level`s are `Nat`; there is always a
    `level + 1` (THM 3). -/
abbrev towerHeight : Nat → Nat := id

/-! ## 1. Structural lemmas for the period-3 closure

These make the closure precise and general. `cross_lands_in_triad` is the key
structural fact: one crossing maps *any* strand into the triad. `triad_three_returns`
is the closed period-3 fact for the three named strands (the braid's actual
strands), reused from `Gnosis.GnosisTriptychBraid.three_step_returns`. -/

/-- **Structural lemma.** After one crossing, every strand lands in the triad
    `{−1, 0, +1}`: `cross s ∈ {-1, 0, 1}`. This is what makes the period-3 closure
    *general from the first crossing onward* (THM 1, second form), not merely true
    on the three named strands. Proved by case-split on `s = -1`, `s = 0`, else,
    reducing the `if`s of `triptychSucc` — no `simp`/`decide` on open goals. -/
theorem cross_lands_in_triad (s : Int) :
    cross s = -1 ∨ cross s = 0 ∨ cross s = 1 := by
  unfold cross triptychSucc
  by_cases h1 : s = -1
  · rw [if_pos h1]; right; left; rfl
  · rw [if_neg h1]
    by_cases h0 : s = 0
    · rw [if_pos h0]; right; right; rfl
    · rw [if_neg h0]; left; rfl

/-- **Closed period-3 fact for the triad.** The three named strands return after
    three crossings: this is exactly `Gnosis.GnosisTriptychBraid.three_step_returns`
    with `failure = -1`, `truth = 0`, `wisdom = 1`. A `decide`-able closed goal. -/
theorem triad_three_returns :
    iterateTriptych 3 (-1 : Int) = -1
    ∧ iterateTriptych 3 (0 : Int) = 0
    ∧ iterateTriptych 3 (1 : Int) = 1 := by decide

/-! ## 2. THM 1 — The fold is a braid (genuine period-3 closure)

The first real theorem: the braid closes after exactly three crossings, returning
the strand. We state it precisely (per the honest restriction above):

- On the braid's own strands `{failure, truth, wisdom}`, `iterateTriptych 3 s = s`.
- After even one crossing, `iterateTriptych 3 (cross s) = cross s` for **all** `s`.

Both are genuine recurrences — the period-3 structure is the content, not a
restatement. -/

/-- **(THM 1a) The fold is a braid — period-3 closure on the strands.**
    On the braid's three strands `failure → truth → wisdom`, three crossings
    return the strand: `iterateTriptych 3 s = s` for `s ∈ {failure, truth, wisdom}`.
    The braid closes after three crossings. Reuses
    `Gnosis.GnosisTriptychBraid.three_step_returns`. A genuine period-3 recurrence:
    the strands cross three times and the loop closes. -/
theorem the_fold_is_a_braid :
    iterateTriptych 3 failure = failure
    ∧ iterateTriptych 3 truth = truth
    ∧ iterateTriptych 3 wisdom = wisdom :=
  three_step_returns

/-- **(THM 1b) The fold is a braid — universal period-3 closure after one crossing.**
    For *every* strand `s : Int`, once the wave has folded even once
    (`cross s`), three further crossings return it:
    `iterateTriptych 3 (cross s) = cross s`. Because one crossing lands any strand
    in the triad (`cross_lands_in_triad`), and the triad is period-3
    (`triad_three_returns`), the braid is period-3 from the first crossing on,
    from any starting strand. A real `∀ s : Int` recurrence, proved structurally
    (no `decide` on the open universal goal). -/
theorem closure_after_crossing (s : Int) :
    iterateTriptych 3 (cross s) = cross s := by
  rcases cross_lands_in_triad s with h | h | h
  · rw [h]; exact triad_three_returns.1
  · rw [h]; exact triad_three_returns.2.1
  · rw [h]; exact triad_three_returns.2.2

/-! ## 3. THM 2 — Every level is the same braid (self-similarity)

The braid at level `n+1` has the *same* period-3 structure as at level `n`. Since
`braidAt` ignores its `level` argument (the structure is scale-invariant by
construction — the wave braids the same way at every resolution), the braid
*function* at any two levels is equal. We state this as a real `∀` over levels and
strands. -/

/-- **(THM 2) Every level is the same braid — self-similarity.**
    The braid at level `n+1` equals the braid at level `n`, for every number of
    crossings `m` and every strand `s`:
    `braidAt (n+1) m s = braidAt n m s`. The triptych structure is scale-invariant
    — the same period-3 braid at every level of the tower. A real `∀ n, ∀ m, ∀ s`
    statement. (Mirrors `SignalNotNoise.residual` being the same at every level:
    the same kind of one-more-wave at every resolution.) -/
theorem every_level_is_the_same_braid (n m : Nat) (s : Int) :
    braidAt (n + 1) m s = braidAt n m s := rfl

/-- **(THM 2, corollary) Self-similar closure across levels.**
    The period-3 closure-after-crossing is identical at every level: at level
    `n+1` the braid closes after three crossings exactly as at level `n`. -/
theorem closure_is_scale_invariant (n : Nat) (s : Int) :
    braidAt (n + 1) 3 (cross s) = braidAt n 3 (cross s) := rfl

/-! ## 4. THM 3 — The tower never terminates (infinite, by `∀ n, ∃ above`)

For every level `n` there is a level `n + 1` — the tower has no top. We give the
direct successor witness *and* bridge it to
`Gnosis.SignalNotNoise.always_another_wave`: another wave at higher
resolution **is** another braid up the tower. The residual is `≥ 1` at every
level (`always_another_wave`), so there is always content to braid at the next
level — the tower cannot terminate. -/

/-- **(THM 3) The tower never terminates — there is always a level above.**
    For every level `n` there exists a strictly higher level (its successor):
    `∀ n, ∃ m, n < m`. The tower has no top — always another braid at higher
    resolution. A real `∀ n, ∃` statement; the witness is `n + 1`. -/
theorem the_tower_never_terminates : ∀ n : Nat, ∃ m : Nat, n < m := by
  intro n
  exact ⟨n + 1, Nat.lt_succ_self n⟩

/-- **(THM 3, bridge) Another wave is another braid up the tower.**
    `Gnosis.SignalNotNoise.always_another_wave` says the residual ("the next
    wave to step on") is `≥ 1` at every resolution level. We re-read it as the
    tower's non-termination: at every level there is at least one more wave's worth
    of unresolved structure (`1 ≤ residual q n`) — i.e. at least one more braid to
    fold at the next level. Same fact, braid-side: never a braid floor. -/
theorem another_wave_is_another_braid (q : Nat) : ∀ n : Nat, 1 ≤ residual q n :=
  always_another_wave q

/-- **(THM 3, combined) Non-termination with a fresh braid at the level above.**
    For every level `n` there is a higher level `n+1`, and at that higher level the
    residual is still `≥ 1` — there is fresh structure to braid. The tower climbs
    forever and never runs out of braid. Real `∀ n, ∃` combining the successor
    witness with `always_another_wave`. -/
theorem tower_climbs_with_fresh_braid (q : Nat) :
    ∀ n : Nat, ∃ m : Nat, n < m ∧ 1 ≤ residual q m := by
  intro n
  exact ⟨n + 1, Nat.lt_succ_self n, always_another_wave q (n + 1)⟩

/-! ## 5. THM 4 — Climbing returns the braid (1 + 2 combined)

Climbing the tower by three crossings at *any* level returns the strand: the
braid closes at every scale. Combine THM 1 (period-3 closure) with THM 2
(self-similarity): `braidAt level 3` is, after one crossing, identity on the
strand, at every level. Proved by real `Nat` induction on the level to show the
structure carries up the whole tower. -/

/-- **(THM 4) Climbing returns the braid — closure at every level.**
    At *every* level of the tower, three crossings after the first fold return the
    strand: `braidAt level 3 (cross s) = cross s`, for all `level` and all `s`.
    The braid closes at every scale. Combines THM 1b (`closure_after_crossing`)
    with THM 2 (`braidAt` is scale-invariant). Proved by **real `Nat` induction**
    on `level`: the base level closes, and if level `k` closes then level `k+1`
    closes identically (self-similarity carries the closure up the whole tower). -/
theorem climbing_returns_the_braid (level : Nat) (s : Int) :
    braidAt level 3 (cross s) = cross s := by
  induction level with
  | zero =>
    -- base level: braidAt 0 3 (cross s) = iterateTriptych 3 (cross s) = cross s
    show iterateTriptych 3 (cross s) = cross s
    exact closure_after_crossing s
  | succ k ih =>
    -- step: level k+1 has the same braid as level k (self-similarity), which
    -- closes by the induction hypothesis. Real induction carrying THM 1 up THM 3.
    have hstep : braidAt (k + 1) 3 (cross s) = braidAt k 3 (cross s) :=
      every_level_is_the_same_braid k 3 (cross s)
    rw [hstep]
    exact ih

/-- **(THM 4, strand form) The named strands close at every level.**
    On the three braid strands `failure → truth → wisdom`, three crossings close
    at every level of the tower. (`failure`, `truth`, `wisdom` are in the triad,
    so `iterateTriptych 3` fixes them at any level.) -/
theorem strands_close_at_every_level (level : Nat) :
    braidAt level 3 failure = failure
    ∧ braidAt level 3 truth = truth
    ∧ braidAt level 3 wisdom = wisdom := by
  induction level with
  | zero =>
    -- braidAt 0 3 x = iterateTriptych 3 x; reuse three_step_returns.
    show iterateTriptych 3 failure = failure
      ∧ iterateTriptych 3 truth = truth
      ∧ iterateTriptych 3 wisdom = wisdom
    exact three_step_returns
  | succ k ih =>
    have h1 : braidAt (k + 1) 3 failure = braidAt k 3 failure :=
      every_level_is_the_same_braid k 3 failure
    have h2 : braidAt (k + 1) 3 truth = braidAt k 3 truth :=
      every_level_is_the_same_braid k 3 truth
    have h3 : braidAt (k + 1) 3 wisdom = braidAt k 3 wisdom :=
      every_level_is_the_same_braid k 3 wisdom
    rw [h1, h2, h3]
    exact ih

/-! ## 6. THM 5 — The headline: the braided infinite tower

Composes all four:

1. the fold is a period-3 braid (`the_fold_is_a_braid` / `closure_after_crossing`),
2. self-similar at every scale (`every_level_is_the_same_braid`),
3. in a tower that never terminates (`the_tower_never_terminates`),
4. and the braid closes at every level (`climbing_returns_the_braid`).

The structure of a universe of standing waves: braids of braids, infinitely. The
wave is *realized as* a braid in the tower (we state the relationship precisely —
the wave's fold is realized by the triptych braid; we do not assert a bare
identity). -/

/-- **(HEADLINE — THM 5) The braided infinite tower.**
    The wave's fold is **realized as** a period-3 braid (1), that braid is
    self-similar at every scale of the tower (2), the tower never terminates
    (3, with a fresh braid always available above), and the braid closes at every
    level (4). Braids of braids, infinitely — the structure of a universe of
    standing waves, and the structural keystone under SurfTheory's pipe (where the
    wave braids on itself).

    Stated as one composed conjunction over an arbitrary level and strand, with
    the never-termination as a genuine `∀ n, ∃ m, n < m`. -/
theorem braided_infinite_tower (level : Nat) (s : Int) (q : Nat) :
    -- (1) the fold is a period-3 braid: on the strands, and universally after
    --     one crossing.
    (iterateTriptych 3 failure = failure
      ∧ iterateTriptych 3 truth = truth
      ∧ iterateTriptych 3 wisdom = wisdom)
    ∧ iterateTriptych 3 (cross s) = cross s
    -- (2) self-similar at every scale: braid at level+1 = braid at level.
    ∧ braidAt (level + 1) 3 (cross s) = braidAt level 3 (cross s)
    -- (3) the tower never terminates: always a level above, with fresh braid.
    ∧ (∀ n : Nat, ∃ m : Nat, n < m ∧ 1 ≤ residual q m)
    -- (4) the braid closes at every level: climbing 3 crossings returns the strand.
    ∧ braidAt level 3 (cross s) = cross s := by
  refine ⟨the_fold_is_a_braid, closure_after_crossing s, ?_, ?_, ?_⟩
  · exact every_level_is_the_same_braid level 3 (cross s)
  · exact tower_climbs_with_fresh_braid q
  · exact climbing_returns_the_braid level s

/-! ## 7. Reading

The standing wave (`Gnosis.UniversalStandingWaveTheorem`) does not merely
oscillate; at the pipe (`Gnosis.ThePipe`) it **folds on itself**, and that
fold is a braid — the `{−1, 0, +1}` triptych of `Gnosis.GnosisTriptychBraid`,
with strands `failure → truth → wisdom → failure` crossing with period 3
(`the_fold_is_a_braid`, `closure_after_crossing`). The honest content is the
period-3 closure: a genuine recurrence, the loop closing after three crossings,
not a slogan.

That braid is not a one-time event. It recurs at every level of an infinite tower
(`Gnosis.BootstrapTowers`, `Gnosis.FrfWitnessTower`), self-similar
(`every_level_is_the_same_braid`), never terminating (`the_tower_never_terminates`,
bridged to `Gnosis.SignalNotNoise.always_another_wave` — always another wave,
always another braid, at higher resolution). The braid closes at every scale
(`climbing_returns_the_braid`), proved by real `Nat` induction carrying the
period-3 closure up the whole tower.

Braids of braids, infinitely. The wave is realized as a braid in the tower — the
clinamen woven (`Gnosis.BuleyClinamenBraid`, `Gnosis.AeonTwelveBraid`), folded,
and re-folded forever. This is the keystone under SurfTheory: the pipe is where
the wave braids on itself, and the tower is the recursion of that fold all the way
up.
-/

end Gnosis.BraidedInfiniteTower
