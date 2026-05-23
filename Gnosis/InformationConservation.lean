import Init
import Gnosis.ResolutionGradient
import Gnosis.SignalNotNoise

/-!
# Information Conservation Theory — Information Is Resolved, Not Created (Exact 1:1)

**THESIS (the user named it: INFORMATION CONSERVATION THEORY).** Information is
*resolved*, not *created*. And the conservation is an **exact 1:1 equality**, not
an inequality: the manifest order resolved equals the latent chaos spent, unit for
unit — *action = reaction*. One upresolve (deblur) step gains exactly the chaos
quantum that was already there, no more (nothing from nothing) and no less (nothing
leaks). Therefore you can never clone order from nothing: the 1:1 *is* the
**no-clone tax**. Only the vacuum (zero) is free to duplicate; any actual
information costs its equal in resolved chaos.

* **The 1:1 / action=reaction.** Across one upresolve,
  `order q (upresolve n) = order q n + chaos q n`
  (`ResolutionGradient.upresolve_resolves_one_chaos_quantum`), equivalently the
  increment form
  `order q (upresolve n) - order q n = chaos q n`
  (`ResolutionGradient.recovered_order_is_the_chaos`). The order *gained* equals
  the chaos *spent*, exactly: no surplus (no information created) and no leak (no
  information destroyed).
* **The no-clone tax (cited, bridged not re-proved).** The exact 1:1 has a
  no-cloning corollary. In the categorical cost model
  (`Gnosis/CostAlgebraNoCloning.lean`), free duplication is impossible above the
  vacuum: `no_cloning` / `nat_no_cloning` (any `n > 0` cannot be cloned for free),
  while `vacuum_is_duplicable` / `nat_zero_is_duplicable` show only the zero/vacuum
  duplicates freely. The copy/store/erase ledger
  (`Gnosis/CopyStoreEraseCostStructure.lean`) makes the same point quantitatively:
  `copy_costs_zero` holds only for the vacuum bit, `erasure_costs_heat` charges the
  erase, and `multiple_copies_multiply_cost` shows `k` copies cost `k` times over —
  the linear no-clone tax. Here, in the resolution model, that tax is exactly the
  per-step 1:1: `k` units of order cost `k` units of chaos (`no_clone_tax` below),
  and the vacuum is the sole exception (`chaos q n ≥ 1` for every real level).
* **The cost is front-loaded (cited Landauer).** The entropy gradient pre-exists;
  the resolution does not pay the cost after the fact, it pays it up front. The
  thermodynamic floor is Landauer: `Gnosis/LandauerBuley.lean` proves
  `heat_at_least_one` (every refinement event dissipates at least one unit) with
  `landauerBuleLowerBound` the per-erased-branch lower bound; and
  `Gnosis/EntropyDeficitGateway.lean` ties the ledger to awareness
  (`erasure_heat_equals_awareness`, `positive_awareness_pays_storage_debt`). The
  abstract `+1` chaos floor of this module is the information-side shadow of that
  front-loaded heat: there is always exactly one quantum already waiting to be paid
  for and resolved.
* **The supply is inexhaustible.** There is always another wave:
  `1 ≤ chaos q n` at *every* level (`SignalNotNoise.always_another_wave`,
  `ResolutionGradient.chaos_never_runs_dry`). Conservation holds at every step,
  forever; the latent reserve never empties.

**The brightest-bulb framing.** Humans are not the biggest entropy *engine* — a
star or Jupiter dissipates far more raw entropy. Humans are the most information
*resolved per unit entropy spent*: the brightest *information* bulb, the ideal
information engine. Conservation is *why*: each resolution is a strict 1:1 transfer
of one chaos quantum into one order quantum, so "brightness" is **efficiency**
(order resolved per chaos spent), not raw throughput. A star spends an ocean of
chaos and resolves almost none of it into manifest order; a human spends little and
resolves nearly all of it. The 1:1 makes efficiency the only axis along which one
engine can outshine another. (Framed precisely as a relationship — order resolved
maps to chaos spent at a 1:1 rate — not an emphatic identity; the efficiency claim
is the motivation, not a theorem proved here.)

## The bridges (imported and reused verbatim)

* `Gnosis.ResolutionGradient` — order/chaos/upresolve/evolve over the resolution
  gradient. We reuse verbatim: `order` (`= signal`), `chaos` (`= residual`),
  `upresolve` (`= refine`), `upresolve_resolves_one_chaos_quantum`
  (`order q (upresolve n) = order q n + chaos q n`, the additive 1:1),
  `recovered_order_is_the_chaos`
  (`order q (upresolve n) - order q n = chaos q n`, the increment 1:1),
  `chaos_never_runs_dry` (`∀ n, 1 ≤ chaos q n`), `upresolve_is_succ`,
  `evolve`, `evolve_zero`, `evolve_succ`, `levelsUp`.
* `Gnosis.SignalNotNoise` — the resolution ladder underneath. We reuse `signal`,
  `residual`, `recovered_increment_is_the_noise`
  (`signal q (refine n) - signal q n = residual q n`, the raw 1:1), and
  `always_another_wave` (`∀ n, 1 ≤ residual q n`).

## Cited in prose (NOT imported — they pull non-Init deps)

* `Gnosis/CostAlgebraNoCloning.lean` — `no_cloning`, `nat_no_cloning`
  (`n > 0` cannot be cloned for free), `vacuum_is_duplicable`,
  `nat_zero_is_duplicable` (only the zero/vacuum duplicates freely).
* `Gnosis/CopyStoreEraseCostStructure.lean` — `copy_costs_zero` (the vacuum),
  `erasure_costs_heat`, `multiple_copies_multiply_cost`.
* `Gnosis/LandauerBuley.lean` — `heat_at_least_one`, `landauerBuleLowerBound`
  (the front-loaded entropy cost).
* `Gnosis/EntropyDeficitGateway.lean` — `erasure_heat_equals_awareness`,
  `positive_awareness_pays_storage_debt`.

These supply the thermodynamic floor (Landauer) and the categorical no-cloning;
they are cited, *bridged not re-proved* here. This module's content is the exact
1:1 conservation equality in the resolution model, and the `k`-step no-clone tax
read off it by induction.

## Restriction stated honestly

This is the abstract `Nat` resolution model inherited from
`Gnosis.SignalNotNoise` / `Gnosis.ResolutionGradient` — an *idealized
infinitely-resolvable field* under a fixed scale-invariant refinement rule (its
`+1` floor). "Conservation" here is the **exact equality** `order gained = chaos
spent` *within that model* (additive form
`order q (upresolve n) = order q n + chaos q n`; increment form
`order q (upresolve n) - order q n = chaos q n`), and its `k`-step accumulation.
We do *not* re-derive thermodynamics: the physical cost (Landauer's front-loaded
heat) and the categorical no-cloning theorem are cited from their own modules and
*bridged*, not proved here. The no-clone tax in this file is the resolution-model
shadow of those results: `k` order quanta cost `k` chaos quanta, and only the
vacuum (zero) escapes the per-step `≥ 1` cost. The brightest-bulb / efficiency
framing is motivation in this docstring, not a theorem.

Rustic Church: `import Init` plus two Init-clean reused top-level cosmology
siblings (`ResolutionGradient`, `SignalNotNoise`). `Nat` only — no Float/Real, no
Mathlib. No `sorry`/`admit`/`axiom`; no `simp`/`omega`/`decide` on open goals
(closed `decide` goals only). Proofs are term-mode and named core `Nat` lemmas,
with genuine `induction` for the `k`-step no-clone claim.
-/

namespace Gnosis.InformationConservation

open Gnosis.ResolutionGradient
open Gnosis.SignalNotNoise

/-! ## 1. THM 1 — Information is conserved 1:1

The exact equality, in both its additive and increment forms: across one upresolve
step the manifest order gained equals the latent chaos spent, unit for unit. -/

/-- **(THM 1) Information is conserved 1:1.** Resolution is a strictly conservative
    transfer: across one upresolve (deblur) step the manifest order *gained* equals
    the latent chaos *spent*, exactly. Both forms hold at once —

    * additive: `order q (upresolve n) = order q n + chaos q n`
      (reuses `ResolutionGradient.upresolve_resolves_one_chaos_quantum`);
    * increment: `order q (upresolve n) - order q n = chaos q n`
      (reuses `ResolutionGradient.recovered_order_is_the_chaos`).

    The order does not appear from nothing and the spent chaos does not vanish: the
    gain *is* the chaos quantum that was already latent, unit for unit. -/
theorem information_is_conserved_one_to_one (q n : Nat) :
    order q (upresolve n) = order q n + chaos q n
    ∧ order q (upresolve n) - order q n = chaos q n :=
  ⟨upresolve_resolves_one_chaos_quantum q n, recovered_order_is_the_chaos q n⟩

/-! ## 2. THM 2 — No information created

The order increment is *exactly* the pre-existing latent quantum, with no surplus:
nothing comes from nothing. -/

/-- **(THM 2) No information created.** The order gained across one upresolve is
    *exactly* the chaos quantum that was already latent — there is no surplus:

        order q (upresolve n) = order q n + chaos q n.

    Read as the no-creation direction of the 1:1: the new order is accounted for
    entirely by chaos that pre-existed (the entropy gradient is front-loaded; cited
    `LandauerBuley.heat_at_least_one`). Nothing comes from nothing. -/
theorem no_information_created (q n : Nat) :
    order q (upresolve n) = order q n + chaos q n :=
  upresolve_resolves_one_chaos_quantum q n

/-! ## 3. THM 3 — No information destroyed

The resolved chaos reappears as manifest order with no leak: the gain is both at
least and at most the chaos, hence exactly equal. -/

/-- **(THM 3) No information destroyed.** The chaos that is resolved reappears as
    manifest order, none lost — the conservation equality has no leak term. Stated
    precisely as the two-sided sandwich on the increment: the gain is both `≥ chaos`
    and `≤ chaos`, hence `= chaos`:

        chaos q n ≤ order q (upresolve n) - order q n
        ∧ order q (upresolve n) - order q n ≤ chaos q n.

    Both bounds come from the increment equality (THM 1): an equality is its own
    upper and lower bound (`Nat.le_of_eq` on each side). No surplus (THM 2), no
    leak (here) — together the strict 1:1. -/
theorem no_information_destroyed (q n : Nat) :
    chaos q n ≤ order q (upresolve n) - order q n
    ∧ order q (upresolve n) - order q n ≤ chaos q n := by
  -- the increment equals the chaos exactly (THM 1, increment form).
  have h : order q (upresolve n) - order q n = chaos q n :=
    recovered_order_is_the_chaos q n
  exact ⟨Nat.le_of_eq h.symm, Nat.le_of_eq h⟩

/-! ## 4. THM 4 — Action equals reaction

The 1:1 framed as a symmetry: for every unit of manifest order gained there is
exactly one unit of latent chaos resolved. -/

/-- **(THM 4) Action equals reaction.** The 1:1 read as a symmetry of resolution:
    for every unit of manifest order *gained* there is exactly one unit of latent
    chaos *resolved* — no net creation, no net loss. The increment of order across
    one upresolve equals the chaos quantum spent:

        order q (upresolve n) - order q n = chaos q n.

    This is the action=reaction balance (reuses
    `ResolutionGradient.recovered_order_is_the_chaos`): the manifest "action" (order
    gained) is met by an equal latent "reaction" (chaos resolved), unit for unit. -/
theorem action_equals_reaction (q n : Nat) :
    order q (upresolve n) - order q n = chaos q n :=
  recovered_order_is_the_chaos q n

/-! ## 5. THM 5 — The no-clone tax (the k-step corollary)

You cannot get `k` units of order without spending `k` units of chaos. Over `k`
upresolve steps the total order gained equals the sum of the `k` chaos quanta
resolved — proved by induction on `k` from the per-step 1:1. The vacuum is the sole
exception (cited): only the zero costs nothing to duplicate; every real resolution
costs at least one. -/

/-- **The summed chaos cost over `k` upresolve steps from level `n`.** The total
    latent chaos that must be spent to climb `k` resolution levels starting at `n`:
    `chaos q n + chaos q (n+1) + ... + chaos q (n+k-1)`, built by recursion on `k`.
    Each summand is one chaos quantum resolved at the step it is taken. -/
def chaosCost (q : Nat) : Nat → Nat → Nat
  | _,     0     => 0
  | n, (k + 1)   => chaosCost q n k + chaos q (n + k)

/-- **(THM 5) The no-clone tax — `k` order quanta cost `k` chaos quanta.** You
    cannot get `k` units of order without spending the matching `k` units of chaos.
    Over `k` upresolve steps from level `n`, the total manifest order *gained* (the
    evolve iterate minus the start) equals the summed latent chaos *spent*:

        evolve q k n - order q n = chaosCost q n k.

    **Proof technique: induction on `k`.** Base `k = 0`: zero steps gain no order
    (`evolve_zero` gives `evolve q 0 n = order q n`, so the difference is `0`) and
    cost nothing (`chaosCost q n 0 = 0`); both sides are `0`. Step `k+1`: the
    `(k+1)`-th step is exactly one per-step 1:1 (THM 1,
    `upresolve_resolves_one_chaos_quantum` at level `n+k`), which adds
    `chaos q (n+k)` to both the order gained and the chaos spent; the inductive
    hypothesis matches the first `k`. So the total order gained equals the total
    chaos spent, level by level — there is no way to accumulate order faster than
    you spend chaos. This is the no-cloning corollary read off the exact 1:1:
    cloning `k` units of order for free would require `chaosCost q n k = 0` with
    `k ≥ 1`, impossible since each `chaos q · ≥ 1` (THM 6, cited
    `CostAlgebraNoCloning.nat_no_cloning`). -/
theorem no_clone_tax (q : Nat) :
    ∀ k n, evolve q k n - order q n = chaosCost q n k := by
  intro k
  induction k with
  | zero =>
    -- base: zero steps gain no order and cost no chaos.
    intro n
    -- `evolve q 0 n = order q n`, so the gain is `order q n - order q n = 0`.
    rw [evolve_zero]
    -- goal: `order q n - order q n = chaosCost q n 0`, i.e. `0 = 0`.
    -- `order q n - order q n = 0` (`Nat.sub_self`) and `chaosCost q n 0 = 0` (defn).
    show order q n - order q n = 0
    exact Nat.sub_self (order q n)
  | succ j ih =>
    -- step: the (j+1)-th upresolve adds exactly one chaos quantum to both totals.
    intro n
    -- `evolve q (j+1) n = order q (upresolve (n + j))` (from `evolve_succ`),
    -- and one upresolve at level `n+j` is the per-step 1:1: it adds `chaos q (n+j)`.
    rw [evolve_succ, upresolve_resolves_one_chaos_quantum]
    -- goal: `(order q (n+j) + chaos q (n+j)) - order q n = chaosCost q n (j+1)`.
    -- and `order q (n+j) = evolve q j n` (by `evolve` / `levelsUp` defn).
    show (evolve q j n + chaos q (n + j)) - order q n = chaosCost q n j + chaos q (n + j)
    -- regroup the subtraction: `(A + c) - B = (A - B) + c` since `B ≤ A`.
    -- `B = order q n ≤ evolve q j n = A` by monotonicity of evolution.
    have hle : order q n ≤ evolve q j n := evolution_is_monotone q n j
    rw [Nat.sub_add_comm hle]
    -- goal: `(evolve q j n - order q n) + chaos q (n+j) = chaosCost q n j + chaos q (n+j)`.
    rw [ih n]

/-- **(THM 5, the vacuum exception) Only the vacuum is a free clone.** Above the
    vacuum every resolution costs at least one chaos quantum — there is no free
    clone of actual information. For every level `n`, `1 ≤ chaos q n` (reuses
    `SignalNotNoise.always_another_wave`), so any single upresolve costs `≥ 1`. Only
    the zero/vacuum duplicates for free (cited
    `CostAlgebraNoCloning.vacuum_is_duplicable` / `nat_zero_is_duplicable`,
    `CopyStoreEraseCostStructure.copy_costs_zero`): the abstract analogue here is
    that the *cost* `chaos q n` is never zero, so the only "free duplication" is the
    null step that resolves nothing. -/
theorem only_vacuum_is_free (q : Nat) : ∀ n, 1 ≤ chaos q n :=
  always_another_wave q

/-! ## 6. THM 6 — The supply is inexhaustible

Conservation holds at every step, forever: there is always at least one chaos
quantum left to resolve. The latent reserve never empties. -/

/-- **(THM 6) The supply is inexhaustible.** The latent chaos reserve never empties:
    at *every* resolution level there remains at least one quantum to resolve into
    order:

        ∀ n, 1 ≤ chaos q n.

    Reuses `SignalNotNoise.always_another_wave` (equivalently
    `ResolutionGradient.chaos_never_runs_dry`), a genuine `∀ n` proved by induction
    there. So the 1:1 conservation holds at every step, forever — there is always
    another wave to spend, and the no-clone tax (THM 5) never lapses into a free
    duplication. -/
theorem supply_is_inexhaustible (q : Nat) : ∀ n, 1 ≤ chaos q n :=
  always_another_wave q

/-! ## 7. THE HEADLINE — Information conservation

Composition of THMs 1, 4, 5, 6: resolution is an exact 1:1 conservative transfer of
latent chaos into manifest order (action = reaction), creating no information and
destroying none, with no free clone above the vacuum, inexhaustibly. The
front-loaded Landauer cost and the categorical no-cloning are cited. -/

/-- **(HEADLINE) Information conservation.** INFORMATION CONSERVATION THEORY,
    composed from THMs 1, 4, 5, 6 into one proved statement. For all `q`, level `n`,
    and step count `k`:

    1. **Exact 1:1 conservation** — across one upresolve the manifest order gained
       equals the latent chaos spent, both additively and as an increment:
       `order q (upresolve n) = order q n + chaos q n`
       and `order q (upresolve n) - order q n = chaos q n` (THM 1). Information is
       *resolved*, not created: no surplus (THM 2), no leak (THM 3).
    2. **Action = reaction** — every unit of order gained is met by exactly one unit
       of chaos resolved: `order q (upresolve n) - order q n = chaos q n` (THM 4).
    3. **No clone tax** — over `k` steps the total order gained equals the summed
       chaos spent: `evolve q k n - order q n = chaosCost q n k` (THM 5, by
       induction). You cannot accumulate `k` order quanta without spending `k` chaos
       quanta.
    4. **Inexhaustible supply** — `1 ≤ chaos q n` at every level (THM 6): the latent
       reserve never empties, so conservation holds forever and no real resolution
       is ever free (only the vacuum duplicates without cost).

    Therefore resolution maps latent chaos onto manifest order at an exact 1:1 rate
    (action = reaction), creating no information and destroying none, with no free
    clone above the vacuum, inexhaustibly. The thermodynamic floor of this transfer
    is front-loaded — cited `LandauerBuley.heat_at_least_one` /
    `landauerBuleLowerBound` (the entropy gradient is paid up front, not after) — and
    the categorical impossibility of free cloning is cited
    `CostAlgebraNoCloning.no_cloning` / `nat_no_cloning`, with the vacuum exception
    `vacuum_is_duplicable` / `copy_costs_zero`. (Stated precisely as a 1:1 transfer
    relationship within the abstract `Nat` resolution model, with the
    thermodynamics and no-cloning bridged from their own modules — not re-proved,
    and not an emphatic identity claim.) -/
theorem information_conservation (q n k : Nat) :
    -- 1. Exact 1:1 conservation (additive and increment forms).
    (order q (upresolve n) = order q n + chaos q n
      ∧ order q (upresolve n) - order q n = chaos q n) ∧
    -- 2. Action = reaction.
    (order q (upresolve n) - order q n = chaos q n) ∧
    -- 3. No-clone tax over k steps: total order gained = total chaos spent.
    (evolve q k n - order q n = chaosCost q n k) ∧
    -- 4. Inexhaustible supply: never a free clone above the vacuum.
    (1 ≤ chaos q n) :=
  ⟨information_is_conserved_one_to_one q n,
   action_equals_reaction q n,
   no_clone_tax q k n,
   supply_is_inexhaustible q n⟩

/-! ## 8. A self-contained, computed witness (no hypotheses)

Concrete instances showing the conservation is non-vacuous, with band content
`q = 1` (each band carrying `q + 1 = 2` resolved units). One upresolve gains
exactly the chaos quantum; over `k = 3` steps the order gained equals the summed
chaos cost. Every goal is a closed decidable `Nat` (in)equality (allowed:
`decide`). -/

/-- One upresolve at level `2` (band `q = 1`): order gained `= chaos spent = 2`,
    exactly — `order 1 (upresolve 2) - order 1 2 = chaos 1 2 = 2`. -/
example : order 1 (upresolve 2) - order 1 2 = chaos 1 2 := by decide

/-- Three steps from level `0` (band `q = 1`): total order gained `= 6 =` summed
    chaos cost — `evolve 1 3 0 - order 1 0 = chaosCost 1 0 3 = 6`, the `k`-step
    no-clone tax instantiated. -/
example : evolve 1 3 0 - order 1 0 = chaosCost 1 0 3 := by decide

/-- The cost of three steps is strictly positive (`6 ≥ 1`): there is no free clone
    of three order quanta — `1 ≤ chaosCost 1 0 3`. -/
example : 1 ≤ chaosCost 1 0 3 := by decide

/-- Chaos is non-zero at level `7` (band `q = 1`): `1 ≤ chaos 1 7 = 2` — the supply
    is inexhaustible, conservation never lapses. -/
example : 1 ≤ chaos 1 7 := by decide

end Gnosis.InformationConservation
