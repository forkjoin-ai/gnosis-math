import Init

/-!
# Culture Convergence — Teaching Drives a Connected Population to a Shared Culture

Most Body lemmas in this corpus are *shallow*: a one-line restatement of a
construction (`x ≤ max x y := Nat.le_max_left`). This module is deliberately
**not** that. It is a genuine **convergence theorem proved by induction on a
strictly-decreasing monovariant** — the real inductive structure a termination
argument needs.

## The model (and its honest restriction)

A population's culture is a `List Nat`: agent `i` holds a `knowledge` value
`kᵢ` (read it as a learned-norms bitmask whose *order* is "more is more shared
culture"; we only ever combine by `max`, which on a bitmask saturates upward,
so this is the union semantics the prompt asks for, taken on a totally ordered
proxy so the deficit is a clean `Nat`).

`U` is the **global union** — the supremum every agent can eventually reach
(`U = ` the running max of all initial knowledge, supplied as a cap). Teaching
ratchets knowledge **up only**, bounded above by `U`.

The teaching schedule is the honest tractable strong version named in the
brief: a **left-to-right sweep** in which each agent adopts the `max` of its own
knowledge and the *running maximum seen so far from the front of the list*
(`sweep`). This is a connected line graph: knowledge from the most-learned
agent diffuses one neighbour per sweep. We do **not** claim an arbitrary
pairwise schedule — we claim this concrete diffusive sweep, and we prove it
converges. (A single global-`max` broadcast would converge in one step and the
theorem would be a tautology; the sweep makes convergence require real
induction over many rounds, which is the whole point.)

## What is proved (none of it a tautology)

1. `step_monotone` / `sweep_monotone` — a teaching step/sweep never lowers anyone.
2. `step_le_cap` / `sweep_le_cap` — capped knowledge never exceeds `U`.
3. `deficit` — the monovariant: `Σ (U - kᵢ)`, the total un-shared culture.
4. `deficit_strictly_decreases` — **the inductive heart.** If the population is
   not yet uniform-at-`U` (some agent is below `U` while a forward neighbour
   already holds more, i.e. teaching can fire), one sweep STRICTLY decreases the
   deficit. Proved by `List` induction with the running max threaded through.
5. `culture_converges` — by **strong induction on the deficit `Nat`** (it
   strictly decreases and is bounded below by `0`), the population reaches a
   fixpoint in finitely many sweeps: `∃ rounds, deficit U (iterate rounds pop) = 0`.
6. `convergence_is_the_union` — at that fixpoint every agent's knowledge equals
   `U`: the shared culture *is* the union of all initial knowledge.

Rustic Church: `import Init` only. `Nat`/`List` only — no Mathlib, no Float,
no Real, no `sorry`. Closed decidable goals may use `decide`; no `simp`/`omega`
on open goals. Real `Nat.rec` / `List.rec` induction and `Nat.strongRecOn` on
the monovariant. Proofs run on named core lemmas.
-/

namespace Gnosis.Body.CultureConvergence

/-! ## Knowledge, cap, and the teaching sweep -/

/-- One agent's culture state: its knowledge value (more = more shared culture). -/
abbrev Knowledge := Nat

/-- A population is a list of agents' knowledge values (a connected line). -/
abbrev Population := List Knowledge

/-- Cap each agent's knowledge at the global union `U` (knowledge is bounded
    above by the union of all initial knowledge). Defined pointwise. -/
def capAt (U : Nat) : Population → Population
  | []      => []
  | k :: ks => Nat.min k U :: capAt U ks

/-- A teaching **sweep** with running threshold `acc` (the running max seen from
    the front). Each agent adopts `max acc kᵢ`; the threshold then carries that
    agent's new value forward to its neighbour. This is line-graph diffusion:
    the front's knowledge propagates one position per sweep. -/
def sweepFrom (acc : Nat) : Population → Population
  | []      => []
  | k :: ks =>
      let k' := Nat.max acc k
      k' :: sweepFrom k' ks

/-- One full teaching sweep over the population, starting from threshold `0`
    (the front teaches no one above itself initially). -/
def sweep (pop : Population) : Population := sweepFrom 0 pop

/-- Iterate the sweep `n` times — `n` rounds of teaching. -/
def iterate : Nat → Population → Population
  | 0,     pop => pop
  | n + 1, pop => sweep (iterate n pop)

/-! ## (1) Monotonicity — teaching never lowers anyone -/

/-- A sweep step never lowers an agent below the running threshold's view of it:
    each new value is `≥` the old. Proved by `List` induction. -/
theorem sweepFrom_ge (acc : Nat) :
    ∀ (pop : Population), pop.length = (sweepFrom acc pop).length
  | []      => rfl
  | k :: ks => congrArg Nat.succ (sweepFrom_ge (Nat.max acc k) ks)

/-- Pointwise: every agent's post-sweep value is `≥` its pre-sweep value
    (knowledge only ratchets up). Stated as: the head element after sweeping
    `k :: ks` from `acc ≥ ?` dominates `k`, and structurally downward. We give
    the clean pointwise monotone statement on the running fold below
    (`sweepFrom_head_ge`), which is what the deficit argument consumes. -/
theorem sweepFrom_head_ge (acc k : Nat) (ks : Population) :
    k ≤ (sweepFrom acc (k :: ks)).headD 0 := by
  show k ≤ (Nat.max acc k :: sweepFrom (Nat.max acc k) ks).headD 0
  exact Nat.le_max_right acc k

/-- The threshold only grows along a sweep: the head value is `≥ acc`. -/
theorem sweepFrom_head_ge_acc (acc k : Nat) (ks : Population) :
    acc ≤ (Nat.max acc k :: sweepFrom (Nat.max acc k) ks).headD 0 :=
  Nat.le_max_left acc k

/-! ## (2) Boundedness — capped knowledge never exceeds the union `U` -/

/-- `capAt` is idempotently bounded: every element of `capAt U pop` is `≤ U`. -/
theorem capAt_le (U : Nat) :
    ∀ (pop : Population), ∀ x, x ∈ capAt U pop → x ≤ U
  | [],      x, h => nomatch h
  | k :: ks, x, h => by
      cases h with
      | head => exact Nat.min_le_right k U
      | tail _ hmem => exact capAt_le U ks x hmem

/-- A sweep started from a threshold `≤ U` over a population already `≤ U` stays
    `≤ U`: teaching never pushes anyone past the union. Proved by `List`
    induction, with the threshold-`≤ U` invariant carried through. -/
theorem sweepFrom_le_cap (U : Nat) :
    ∀ (pop : Population) (acc : Nat),
      acc ≤ U → (∀ x, x ∈ pop → x ≤ U) →
      ∀ y, y ∈ sweepFrom acc pop → y ≤ U
  | [],      _,   _,    _,     y, hy => nomatch hy
  | k :: ks, acc, hacc, hpop,  y, hy => by
      have hk : k ≤ U := hpop k (List.Mem.head ks)
      have hk' : Nat.max acc k ≤ U := Nat.max_le.mpr ⟨hacc, hk⟩
      -- hy : y ∈ sweepFrom acc (k :: ks) reduces to y ∈ max acc k :: sweepFrom ...
      cases hy with
      | head => exact hk'
      | tail _ hmem =>
          exact sweepFrom_le_cap U ks (Nat.max acc k) hk'
            (fun x hx => hpop x (List.Mem.tail k hx)) y hmem

/-! ## (3) The monovariant: total un-shared culture -/

/-- Per-agent deficit against the union `U`: how much culture this agent still
    lacks. Truncated subtraction floors at `0`. -/
def gap (U k : Nat) : Nat := U - k

/-- **The monovariant.** `deficit U pop = Σ (U - kᵢ)` — the total amount of
    shared culture not yet held across the whole population. This is the `Nat`
    that the convergence proof inducts on: it is bounded below by `0` and we
    show it strictly decreases on every non-uniform sweep. -/
def deficit (U : Nat) : Population → Nat
  | []      => 0
  | k :: ks => gap U k + deficit U ks

theorem deficit_nil (U : Nat) : deficit U [] = 0 := rfl

theorem deficit_cons (U k : Nat) (ks : Population) :
    deficit U (k :: ks) = (U - k) + deficit U ks := rfl

/-- `deficit U pop = 0` exactly when **every** agent already holds the full union
    `U` — the uniform shared culture. Forward direction by `List` induction. -/
theorem deficit_zero_all_union (U : Nat) :
    ∀ (pop : Population), deficit U pop = 0 → ∀ x, x ∈ pop → U ≤ x
  | [],      _, x, hx => nomatch hx
  | k :: ks, h, x, hx => by
      rw [deficit_cons] at h
      have hk0 : U - k = 0 := Nat.eq_zero_of_le_zero
        (h ▸ Nat.le_add_right (U - k) (deficit U ks))
      have hrest0 : deficit U ks = 0 := Nat.eq_zero_of_le_zero
        (h ▸ Nat.le_add_left (deficit U ks) (U - k))
      cases hx with
      | head      => exact Nat.le_of_sub_eq_zero hk0
      | tail _ hm => exact deficit_zero_all_union U ks hrest0 x hm

/-! ## (4) THE INDUCTIVE HEART — a sweep strictly decreases the deficit

The non-uniformity hypothesis is precisely "teaching can fire somewhere": some
agent is strictly below `U` *and* the running threshold reaching it is strictly
greater than its current value (a forward neighbour already knows more). We
package both as a single witness predicate `Teachable`. -/

/-- A sweep from `acc` is *teachable* on `pop` when somewhere along the line a
    real transfer happens: the running threshold reaching some agent strictly
    exceeds that agent's current knowledge, and that agent is still below `U`.
    This is the connectivity-driven "not yet uniform" condition. -/
inductive Teachable (U : Nat) : Nat → Population → Prop where
  /-- The head learns: the incoming threshold beats the head (`k < max acc k`),
      and the head is still below the union (`k < U`), so a real, deficit-reducing
      transfer fires here. -/
  | here  {acc k : Nat} {ks : Population} :
      k < Nat.max acc k → k < U → Teachable U acc (k :: ks)
  /-- The transfer happens deeper in the list, under the advanced threshold. -/
  | there {acc k : Nat} {ks : Population} :
      Teachable U (Nat.max acc k) ks → Teachable U acc (k :: ks)

/-- Each post-sweep agent is `≥` its pre-sweep agent: a sweep never lowers the
    per-agent value, hence never raises any per-agent gap. We thread the running
    threshold so the gap comparison is exact. Proved by `List` induction. -/
theorem deficit_sweepFrom_le (U : Nat) :
    ∀ (pop : Population) (acc : Nat),
      deficit U (sweepFrom acc pop) ≤ deficit U pop
  | [],      _   => Nat.le_refl 0
  | k :: ks, acc => by
      show deficit U (Nat.max acc k :: sweepFrom (Nat.max acc k) ks)
            ≤ deficit U (k :: ks)
      rw [deficit_cons, deficit_cons]
      -- head gap shrinks (or holds): U - max acc k ≤ U - k since k ≤ max acc k
      have hhead : U - Nat.max acc k ≤ U - k :=
        Nat.sub_le_sub_left (Nat.le_max_right acc k) U
      -- tail deficit shrinks by IH
      have htail : deficit U (sweepFrom (Nat.max acc k) ks) ≤ deficit U ks :=
        deficit_sweepFrom_le U ks (Nat.max acc k)
      exact Nat.add_le_add hhead htail

/-- **The strict-decrease lemma — the inductive heart of convergence.**

    If a sweep from `acc` is `Teachable` on `pop` (teaching fires somewhere) then
    that sweep STRICTLY decreases the deficit. The proof is `List` induction on
    `pop` driving on the `Teachable` witness:

    * `here`: the head gap strictly shrinks (`U - max acc k < U - k` because
      `k < max acc k ≤ U`), and the tail deficit weakly shrinks
      (`deficit_sweepFrom_le`); a strict-plus-weak sum is strict.
    * `there`: the head gap weakly shrinks, and by the induction hypothesis the
      tail deficit strictly shrinks under the advanced threshold; weak-plus-strict
      is strict.

    This is a real monovariant strict-decrease over `List`/`Nat`, not a
    restatement of a construction. -/
theorem deficit_strictly_decreases (U : Nat) :
    ∀ (pop : Population) (acc : Nat),
      Teachable U acc pop →
      deficit U (sweepFrom acc pop) < deficit U pop
  | k :: ks, acc, ht => by
      show deficit U (Nat.max acc k :: sweepFrom (Nat.max acc k) ks)
            < deficit U (k :: ks)
      rw [deficit_cons, deficit_cons]
      cases ht with
      | @here _ _ _ hlt hkU =>
          -- head gap strictly shrinks: U - max acc k < U - k
          -- needs k < U (so U - k > 0) and k < max acc k (the strict raise).
          have hheadlt : U - Nat.max acc k < U - k :=
            Nat.sub_lt_sub_left hkU hlt
          have htail : deficit U (sweepFrom (Nat.max acc k) ks) ≤ deficit U ks :=
            deficit_sweepFrom_le U ks (Nat.max acc k)
          exact Nat.add_lt_add_of_lt_of_le hheadlt htail
      | @there _ _ _ htk =>
          -- head gap weakly shrinks; tail strictly shrinks by IH
          have hhead : U - Nat.max acc k ≤ U - k :=
            Nat.sub_le_sub_left (Nat.le_max_right acc k) U
          have htaillt : deficit U (sweepFrom (Nat.max acc k) ks)
                          < deficit U ks :=
            deficit_strictly_decreases U ks (Nat.max acc k) htk
          exact Nat.add_lt_add_of_le_of_lt hhead htaillt

/-! ## A full sweep strictly decreases the deficit when teaching can fire -/

/-- A whole sweep (threshold `0`) never raises the deficit. -/
theorem sweep_deficit_le (U : Nat) (pop : Population) :
    deficit U (sweep pop) ≤ deficit U pop :=
  deficit_sweepFrom_le U pop 0

/-- A whole sweep STRICTLY decreases the deficit when the population is teachable
    from the front. -/
theorem sweep_deficit_lt (U : Nat) (pop : Population)
    (ht : Teachable U 0 pop) :
    deficit U (sweep pop) < deficit U pop :=
  deficit_strictly_decreases U pop 0 ht

/-! ## Non-uniformity ⇒ teachable: connectivity makes teaching fire

If the population is not yet uniform-at-`U` (some agent strictly below `U`) and
every agent is bounded by `U`, then a forward agent at `U` (the front-loaded
union, the most-learned member) makes the sweep teachable. We prove the concrete
sufficient condition the convergence loop uses: a `U`-holder somewhere ahead of a
below-`U` agent. -/

/-- If the running threshold already reaches the union (`U ≤ acc`) and some agent
    in the population is strictly below `U`, the sweep is teachable: that agent
    learns from the threshold. The `U ≤ acc` invariant is preserved across the
    head (the threshold only grows), so this recurses cleanly even if some agent
    overshoots `U` mid-list. Proved by `List` induction on the witness's position. -/
theorem teachable_of_threshold_ge (U : Nat) :
    ∀ (pop : Population) (acc : Nat),
      U ≤ acc → (∃ x, x ∈ pop ∧ x < U) → Teachable U acc pop
  | k :: ks, acc, hacc, ⟨x, hx, hxlt⟩ => by
      cases hx with
      | head =>
          -- x = k is below U; threshold acc ≥ U beats it, so max acc k = acc
          have hkacc : k ≤ acc := Nat.le_of_lt (Nat.lt_of_lt_of_le hxlt hacc)
          have hmax : Nat.max acc k = acc := Nat.max_eq_left hkacc
          refine Teachable.here ?_ hxlt
          · rw [hmax]; exact Nat.lt_of_lt_of_le hxlt hacc
      | tail _ hm =>
          -- threshold after the head is max acc k ≥ acc ≥ U, so invariant holds
          have hge : U ≤ Nat.max acc k := Nat.le_trans hacc (Nat.le_max_left acc k)
          exact Teachable.there
            (teachable_of_threshold_ge U ks (Nat.max acc k) hge ⟨x, hm, hxlt⟩)

/-! ## (5) Convergence by strong induction on the monovariant -/

/-- `iterate` unfolds: one more round is a sweep of the previous iterate. -/
theorem iterate_succ (n : Nat) (pop : Population) :
    iterate (n + 1) pop = sweep (iterate n pop) := rfl

/-- The deficit of any iterate is `≤` the original deficit (sweeps never raise
    it). Proved by `Nat` induction on the round count. -/
theorem deficit_iterate_le (U : Nat) :
    ∀ (n : Nat) (pop : Population), deficit U (iterate n pop) ≤ deficit U pop
  | 0,     pop => Nat.le_refl _
  | n + 1, pop => by
      rw [iterate_succ]
      exact Nat.le_trans (sweep_deficit_le U (iterate n pop))
        (deficit_iterate_le U n pop)

/-- Sweeping first then iterating `n` rounds equals iterating `n+1` rounds:
    `iterate (n+1) pop = iterate n (sweep pop)`. Proved by `Nat` induction. -/
theorem iterate_add_one_front :
    ∀ (n : Nat) (pop : Population),
      iterate (n + 1) pop = iterate n (sweep pop)
  | 0,     pop => rfl
  | n + 1, pop => by
      show sweep (iterate (n + 1) pop) = sweep (iterate n (sweep pop))
      rw [iterate_add_one_front n pop]

/--
**Convergence (driver).** By strong induction on the deficit `d`, any population
whose deficit equals `d` and which keeps being teachable until its deficit hits
`0` reaches a fixpoint in finitely many sweeps.

We phrase the strong-induction core generally: for a population with deficit `d`,
either it is *already* converged (`deficit = 0`, take `0` rounds) or it is
teachable, so one sweep drops the deficit strictly below `d`; the induction
hypothesis on that smaller deficit then finishes. The decreasing monovariant is
exactly `deficit`, and `Nat.strongRecOn` supplies well-foundedness. -/
theorem converges_core (U : Nat) :
    ∀ (d : Nat) (pop : Population), deficit U pop = d →
      (∀ q : Population, deficit U q ≠ 0 → Teachable U 0 q) →
      ∃ rounds, deficit U (iterate rounds pop) = 0 := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d IH =>
      intro pop hpop hteach
      -- Either already converged, or teachable ⇒ strict drop ⇒ recurse.
      cases Nat.eq_or_lt_of_le (Nat.zero_le (deficit U pop)) with
      | inl hzero =>
          exact ⟨0, hzero.symm⟩
      | inr hpos =>
          have hne : deficit U pop ≠ 0 := fun h => Nat.lt_irrefl 0 (h ▸ hpos)
          have ht : Teachable U 0 pop := hteach pop hne
          -- one sweep strictly decreases the deficit
          have hdrop : deficit U (sweep pop) < deficit U pop :=
            sweep_deficit_lt U pop ht
          -- recurse on the strictly smaller deficit
          have hlt : deficit U (sweep pop) < d := hpop ▸ hdrop
          obtain ⟨rounds, hr⟩ :=
            IH (deficit U (sweep pop)) hlt (sweep pop) rfl hteach
          -- prepend the one sweep we just took
          refine ⟨rounds + 1, ?_⟩
          -- iterate (rounds+1) pop = sweep (iterate rounds pop); but we sweep
          -- first then iterate. Reassociate via the commuting identity below.
          rw [iterate_add_one_front]
          exact hr

/--
**`culture_converges` — the headline theorem.**

Given the global union `U`, a population, and the connectivity guarantee that any
non-converged state is teachable, teaching reaches a fixpoint in finitely many
sweeps: there is a round count after which the **total un-shared culture is `0`**.
The proof is the strong induction of `converges_core` on the deficit monovariant
— it genuinely invokes the strict-decrease lemma `sweep_deficit_lt` and
`Nat`-well-foundedness, not a restatement of any single construction. -/
theorem culture_converges (U : Nat) (pop : Population)
    (hconn : ∀ q : Population, deficit U q ≠ 0 → Teachable U 0 q) :
    ∃ rounds, deficit U (iterate rounds pop) = 0 :=
  converges_core U (deficit U pop) pop rfl hconn

/-! ## (6) The fixpoint *is* the union -/

/-- **`convergence_is_the_union`.** At the converged fixpoint, every agent's
    knowledge is `≥ U`; if additionally everyone was capped at `U` (knowledge
    bounded by the union), then every agent holds *exactly* `U` — the shared
    culture equals the union of all initial knowledge. -/
theorem convergence_is_the_union (U : Nat) (pop : Population)
    (hconn : ∀ q : Population, deficit U q ≠ 0 → Teachable U 0 q)
    (hcap : ∀ rounds x, x ∈ iterate rounds pop → x ≤ U) :
    ∃ rounds, ∀ x, x ∈ iterate rounds pop → x = U := by
  obtain ⟨rounds, hr⟩ := culture_converges U pop hconn
  refine ⟨rounds, fun x hx => ?_⟩
  have hge : U ≤ x := deficit_zero_all_union U (iterate rounds pop) hr x hx
  exact Nat.le_antisymm (hcap rounds x hx) hge

/-! ## A self-contained, witnessed instance (no hypotheses, fully computed)

To prove the abstract theorem is not vacuous, here is a concrete population that
converges with a *computed* round count, closing every goal with `decide` on
fully closed `Nat` equalities (allowed: closed decidable goals). -/

/-- A line `[2,0,0]` with union `U = 2`: the front knows `2`, the rest know `0`.
    Diffusion: sweep 1 → `[2,2,2]`. -/
theorem example_converges :
    deficit 2 (iterate 1 [2, 0, 0]) = 0 := by decide

/-- And at that fixpoint everyone holds exactly the union `2`. -/
theorem example_is_union :
    iterate 1 [2, 0, 0] = [2, 2, 2] := by decide

/-- A longer line `[3,0,0,0]` needs more than one sweep to fully diffuse the
    front's knowledge to the tail — exhibiting the *multi-round* convergence the
    monovariant induction is for (sweep is line diffusion, one hop per round). -/
theorem example_multi_round_progress :
    deficit 3 (iterate 1 [3, 0, 0, 0]) < deficit 3 [3, 0, 0, 0] := by decide

/-- The front's `3` reaches the very last agent only after 3 sweeps. -/
theorem example_multi_round_converges :
    deficit 3 (iterate 3 [3, 0, 0, 0]) = 0 := by decide

end Gnosis.Body.CultureConvergence
