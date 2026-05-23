import Init
import Gnosis.Body.SelectionConvergesToLife

/-!
# If You Can't Beat Them, Join Them — Joining Is a (Necessarily) Dominant Strategy

`Gnosis.Body.SelectionConvergesToLife` proves that iterated selection is a
dynamical system whose global attractor is the life-supporting fixpoint `L`: the
*selection step* `stepOne L f = min (f + 1) L` pulls every below-`L` fitness one
rung toward the attractor, and iterating it drives any population to `L`
(`selection_converges_to_life`). That module is about a *population* converging.

This module reads the very same `stepOne` move from the point of view of a *single
agent* facing leaders who already sit at the attractor `L`, and proves the folk
maxim **"if you can't beat them, join them"** is not folklore but a genuine
**dominance result** in the game-theoretic sense — necessarily, as a corollary of
the selection dynamics.

## The model

An agent has fitness `f`; the leaders sit at the life attractor `L`. The agent
picks one of two actions:

* `resist f := f` — stand pat, keep your current fitness.
* `join f L := stepOne L f` — adopt the winning move: take exactly one selection
  step toward the leaders (the *same* `stepOne` the convergence proof iterates).

The predicate `cantBeat f L := f < L` says you genuinely cannot exceed the
leaders — you are strictly below the attractor.

## What is proved (a real dominance result, not a tautology)

1. `join_weakly_dominates` — for any in-model agent (`f ≤ L`), joining is **never
   worse** than resisting: `resist f ≤ join f L`. A *weakly* dominant action,
   holding across the whole feasible range. The honest hypothesis is `f ≤ L`
   (the agent is at or below the attractor — an agent already *past* `L` is out
   of model, and `join` would pull it *down* to `L`).
2. `join_strictly_dominates` — when you genuinely `cantBeat` them (`f < L`),
   joining is **strictly** better: `resist f < join f L`. This is the bite of the
   maxim: below the leaders, the join move strictly improves you.
3. `join_is_dominant` — bundles 1 + 2: joining weakly dominates always (for
   `f ≤ L`) and strictly dominates exactly when you can't beat them. This is the
   textbook signature of a (weakly, and on the relevant region strictly) dominant
   strategy.
4. `joining_converges_to_them` — the bridge to the dynamics: a population that
   *all joins* (iterates the selection step) converges to the leaders' level `L`
   — because the join move **is** the selection step, this is exactly
   `selection_converges_to_life`. Resisters, by contrast, never close the gap
   (`resisting_never_closes_the_gap`): standing pat leaves the deficit fixed.
5. `if_you_cant_beat_them_join_them` — the headline: when `cantBeat f L`, `join`
   *strictly* dominates `resist` **and** the all-join population converges to the
   attractor. So joining is the dominant strategy, necessarily, by composing the
   strict-dominance step (2) with the convergence bridge (4).
6. A concrete computed witness (`f = 1`, `L = 3`): `join 1 3 = 2 > 1 = resist 1`.

Rustic Church: `import Init` and `Gnosis.Body.SelectionConvergesToLife` only.
`Nat` only — no Mathlib, no Float, no Real, no `sorry`. Term-mode with named core
`Nat` lemmas; closed decidable goals may use `decide`; no `simp`/`omega` on open
goals.
-/

namespace Gnosis.Body.IfYouCantBeatThem

open Gnosis.Body.SelectionConvergesToLife

/-! ## The agent, the leaders, and the two actions -/

/-- You **cannot beat the leaders**: your fitness `f` sits strictly below the
    attractor `L` where the leaders rest. This is the precondition of the maxim —
    if you *could* beat them (`L ≤ f`) there would be nothing to join. Reducible
    so its decidability transfers from the underlying `f < L` (a closed instance
    can then be settled by `decide`). -/
@[reducible] def cantBeat (f L : Nat) : Prop := f < L

/-- **Join them.** Adopt the winning move: take exactly one selection step toward
    the leaders' level `L`. This is literally `SelectionConvergesToLife.stepOne`,
    the per-step engine the convergence proof iterates — joining the leaders *is*
    one round of the selection dynamics applied to yourself. -/
def join (f L : Nat) : Nat := stepOne L f

/-- **Resist.** Stand pat — keep your current fitness, refuse to adopt the
    leaders' move. The do-nothing action. -/
def resist (f : Nat) : Nat := f

/-! ## (1) Weak dominance — joining is never worse than resisting -/

/--
**`join_weakly_dominates`.** For any in-model agent (fitness at or below the
attractor, `f ≤ L`), joining is **never worse** than resisting:
`resist f ≤ join f L`, i.e. `f ≤ min (f + 1) L`.

The proof is the join of two facts via `Nat.le_min_of_le_of_le`: `f ≤ f + 1`
(`Nat.le_succ`) and `f ≤ L` (the hypothesis). So `join` is a *weakly dominant*
action across the whole feasible region — there is never a state where standing
pat does strictly better than adopting the leaders' move.

The `f ≤ L` hypothesis is honest, not cosmetic: an agent already *past* the
attractor (`L < f`) is out of model, and there `join` would pull it *down* to
`L`, so it would fail to weakly dominate. We claim dominance exactly on the
feasible region. -/
theorem join_weakly_dominates (f L : Nat) (h : f ≤ L) : resist f ≤ join f L :=
  -- `resist f = f`, `join f L = stepOne L f = Nat.min (f + 1) L`.
  -- `f ≤ min (f+1) L` from `f ≤ f+1` and `f ≤ L`.
  Nat.le_min_of_le_of_le (Nat.le_succ f) h

/-! ## (2) Strict dominance — when you can't beat them, joining is strictly better -/

/--
**`join_strictly_dominates`.** When you genuinely `cantBeat` the leaders
(`f < L`), joining is **strictly** better than resisting:
`resist f < join f L`, i.e. `f < min (f + 1) L`.

The proof: `f < L` is *definitionally* `f + 1 ≤ L`, so `Nat.min_eq_left` collapses
`min (f + 1) L` to `f + 1`; then `Nat.lt_succ_self` gives `f < f + 1`. This is the
bite of the maxim — below the leaders, taking their move strictly improves you;
resisting strictly underperforms. -/
theorem join_strictly_dominates (f L : Nat) (h : cantBeat f L) :
    resist f < join f L := by
  -- `cantBeat f L` unfolds to `f < L`, defeq `f + 1 ≤ L`.
  unfold cantBeat at h
  show f < stepOne L f
  unfold stepOne
  -- `f < L` is `f + 1 ≤ L`, so `Nat.min (f+1) L = f + 1`.
  have hmin : Nat.min (f + 1) L = f + 1 := Nat.min_eq_left h
  rw [hmin]
  exact Nat.lt_succ_self f

/-! ## (3) The dominance bundle -/

/--
**`join_is_dominant`.** Joining dominates resisting in the full game-theoretic
sense: it is **weakly** dominant everywhere on the feasible region (`f ≤ L` ⇒
`resist f ≤ join f L`) and **strictly** dominant exactly when you cannot beat the
leaders (`cantBeat f L` ⇒ `resist f < join f L`). Bundles (1) and (2). This is the
textbook signature of a (weakly, strict-on-the-relevant-region) dominant
strategy: never worse, and strictly better whenever the maxim's hypothesis
holds. -/
theorem join_is_dominant (f L : Nat) :
    (f ≤ L → resist f ≤ join f L) ∧ (cantBeat f L → resist f < join f L) :=
  ⟨join_weakly_dominates f L, join_strictly_dominates f L⟩

/-! ## (4) The convergence bridge — joining gets you to their level -/

/--
**`joining_converges_to_them`.** A population that *all joins* — every member
iterates the join move, which **is** the selection step `stepOne` — converges to
the leaders' level `L` (the attractor) in finitely many rounds: the total
distance from `L` reaches `0`. This is *exactly*
`SelectionConvergesToLife.selection_converges_to_life`, re-read as a statement
about agents adopting the winning move: because `join = stepOne`, the all-join
trajectory is the selection trajectory, and the selection trajectory converges to
the attractor.

So joining doesn't merely beat resisting locally (3) — it *gets you there*: the
basin of attraction of the all-join dynamics is the leaders' level itself. -/
theorem joining_converges_to_them (L : Nat) (pop : Population) :
    ∃ steps, lifeDeficit L (iterate L steps pop) = 0 :=
  selection_converges_to_life L pop

/--
**`resisting_never_closes_the_gap`.** The contrast that makes joining
*necessarily* dominant: a resister stands pat, so its distance from the leaders is
exactly its starting gap — resisting changes nothing, `resist f = f`, hence the
gap `L - resist f = L - f` is identical. If you genuinely can't beat them
(`f < L`) the gap is strictly positive (`0 < L - f`) and resisting leaves it that
way forever. The do-nothing action provably never converges to the attractor when
it starts below it. -/
theorem resisting_never_closes_the_gap (f L : Nat) (h : cantBeat f L) :
    L - resist f = L - f ∧ 0 < L - resist f := by
  unfold cantBeat at h
  show L - f = L - f ∧ 0 < L - f
  exact ⟨rfl, Nat.zero_lt_sub_of_lt h⟩

/-! ## (5) The headline -/

/--
**`if_you_cant_beat_them_join_them` — the headline theorem.**

When you genuinely cannot beat the leaders (`cantBeat f L`), the join move

* **strictly dominates** resisting — `resist f < join f L` (joining is strictly
  better, by `join_strictly_dominates`), and
* **converges to the leaders' level** — the all-join population reaches the
  attractor `L` in finitely many rounds (`joining_converges_to_them`, i.e. the
  selection dynamics), for any starting population.

So joining is the (necessarily) dominant strategy: it is strictly better in the
one-shot comparison *and* it provably brings you to the leaders' level under
iteration — composing the strict-dominance step (2) with the convergence bridge
(4). The maxim is a corollary of selection-converges-to-life, not a tautology. -/
theorem if_you_cant_beat_them_join_them (f L : Nat) (pop : Population)
    (h : cantBeat f L) :
    resist f < join f L
      ∧ (∃ steps, lifeDeficit L (iterate L steps pop) = 0) :=
  ⟨join_strictly_dominates f L h, joining_converges_to_them L pop⟩

/-! ## (6) A self-contained, computed witness (no hypotheses)

A concrete instance proving the maxim is non-vacuous: a follower at fitness `1`
facing leaders at `L = 3`. The agent cannot beat them (`1 < 3`); joining takes one
step to `2`, strictly better than resisting at `1`. Every goal is a closed
decidable `Nat` equality / inequality (allowed: `decide`). -/

/-- The follower `f = 1` cannot beat leaders at `L = 3`. -/
example : cantBeat 1 3 := by decide

/-- Joining strictly beats resisting for that follower: `join 1 3 = 2 > 1`. -/
example : resist 1 < join 1 3 := by decide

/-- The exact values: resisting holds `1`, joining advances to `2`. -/
example : resist 1 = 1 ∧ join 1 3 = 2 := by decide

end Gnosis.Body.IfYouCantBeatThem
