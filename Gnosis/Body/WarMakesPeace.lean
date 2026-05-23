import Init
import Gnosis.Body.RedQueen

/-!
# War Makes Peace — Deterrence as a Contrarian Theorem

>   A graver threat grows the peacemaking set.

The epigraph is the theorem: as the walkaway (war) grows graver, the set of deals
that make the peace only grows — peacemaking by deterrence (see `war_makes_peace`).

A contrarian theorem in the house tradition (cf.
`Gnosis/Contrarian/ContrarianAdversariesImprove.lean`,
`Gnosis/Contrarian/ContrarianSinIsWisdom.lean`): the *threat* of war is what
manufactures peace. Not its execution — its credibility. This is **deterrence**.

The bridge is to negotiation. In `Gnosis/NegotiationEquilibrium.lean` the
walkaway is the BATNA — the Best Alternative To a Negotiated Agreement, the
value of *not* taking the deal. "BATNA walking is void walking": the walkaway is
the floor below which no party will go, the reservation price against which every
offer is judged. A deal holds the peace exactly when it beats the walkaway.

Here the walkaway is **war**. A party can always walk away from the table and
fight. The walkaway therefore carries a base value `base` (what fighting could
win on paper) discounted by the *expected cost of violence*: with probability
`violence` (out of 100) the walkaway turns into actual war at cost `warCost`.

  walkawayValue base violence warCost = base - (violence * warCost) / 100

The contrarian engine: **the more dangerous the walkaway, the worse the outside
option, the more deals clear the bar of peace-acceptability.** Raise the threat
of war and the reservation price *falls* — so deals that were marginal under a
mild threat become acceptable under a grave one. The acceptable set only grows.
At total war (`violence = 100`, `warCost ≥ base`) the walkaway is worth `0` and
*every* non-negative deal keeps the peace. Peace is hardest precisely when
walking away is *safe* (`violence = 0`): then only deals worth the full `base`
survive.

This mirrors the Red Queen (`Gnosis/Body/RedQueen.lean`): conflict is zero-sum
(`coevolution_is_zero_sum`), and escalation *past* grit is pyrrhic — pushing
predator pressure beyond prey grit starves the predator on the corpses
(`over_push_is_pyrrhic`). So the *execution* of total war destroys both sides;
it is the credible-but-costly *threat* — held at the boundary, never paid — that
yields the peace. War made peace by not being fought.

Rustic Church: `Init` only (+ sibling Body module `RedQueen`). No Mathlib.
`Nat` arithmetic, with `Int` only where a signed value is genuine. No `sorry`;
no `simp`/`decide`/`omega` on open goals — term-mode and named core lemmas only.
-/

namespace Gnosis.Body.WarMakesPeace

open Gnosis.Body.RedQueen

/-! ## 1. The walkaway (BATNA = war) and its value -/

/-- **The value of the walkaway.** A party can always walk away from the table
    and fight. On paper the fight is worth `base`, but with probability
    `violence` (out of 100) it turns into real war at cost `warCost`, so the
    expected cost of violence `(violence * warCost) / 100` is subtracted. `Nat`
    truncation floors the value at `0`: a sufficiently dangerous walkaway is
    worth nothing. This is the reservation price — the BATNA of
    `NegotiationEquilibrium` with war as the alternative. -/
def walkawayValue (base violence warCost : Nat) : Nat :=
  base - (violence * warCost) / 100

/-- **Peace-acceptability.** A deal of value `deal` keeps the peace iff it beats
    the walkaway: a rational party prefers the deal to fighting exactly when the
    deal is worth at least as much as its outside option. Mirrors the BATNA
    boundary — below the walkaway, "walking is void walking". -/
def peacemaking (deal base violence warCost : Nat) : Prop :=
  walkawayValue base violence warCost ≤ deal

/-! ## 2. A graver threat lowers the value of walking away -/

/-- **The walkaway falls with violence.** More likely violence ⇒ a larger
    expected war cost ⇒ a smaller walkaway value: a worse outside option. The
    threat of war degrades the very alternative a party would walk to. Proved by
    pushing `v1 ≤ v2` through the multiplication (`Nat.mul_le_mul_right`), the
    division (`Nat.div_le_div_right`), and the truncated subtraction
    (`Nat.sub_le_sub_left`) — note the subtraction *reverses* the order, which is
    exactly the contrarian twist. -/
theorem walkaway_falls_with_violence
    (base warCost v1 v2 : Nat) (h : v1 ≤ v2) :
    walkawayValue base v2 warCost ≤ walkawayValue base v1 warCost := by
  unfold walkawayValue
  -- v1 * warCost ≤ v2 * warCost
  have hmul : v1 * warCost ≤ v2 * warCost := Nat.mul_le_mul_right warCost h
  -- (v1 * warCost) / 100 ≤ (v2 * warCost) / 100
  have hdiv : v1 * warCost / 100 ≤ v2 * warCost / 100 := Nat.div_le_div_right hmul
  -- subtraction on the left of a fixed `base` reverses the inequality
  exact Nat.sub_le_sub_left hdiv base

/-- **The reservation price is monotone non-increasing in violence.** The price
    below which a party walks (= `walkawayValue`) never rises as the threat of
    war grows; it can only fall or hold. A direct corollary of
    `walkaway_falls_with_violence`, named for the negotiation reading: the
    reservation price is what the deal must beat, and the threat of war pushes
    that bar *down*. -/
theorem peace_reservation_falls_with_violence
    (base warCost v1 v2 : Nat) (h : v1 ≤ v2) :
    walkawayValue base v2 warCost ≤ walkawayValue base v1 warCost :=
  walkaway_falls_with_violence base warCost v1 v2 h

/-! ## 3. The headline contrarian theorem: war makes peace -/

/-- **War makes peace.** *The* contrarian theorem. If `v1 ≤ v2` (a graver threat
    of war) then any deal that secured peace under the milder threat `v1` still
    secures it under the graver threat `v2`. Because the reservation price *falls*
    with violence, the bar a deal must clear drops, so the set of
    peace-acceptable deals only **grows** as war looms closer.

    The more dangerous the walkaway — the closer war — the more deals are
    accepted. The threat of war manufactures peace: facing a worse alternative,
    parties settle for terms they would otherwise have fought over. Deterrence.

    Proved by `Nat.le_trans`: the new (lower) reservation price ≤ the old
    reservation price ≤ `deal`. -/
theorem war_makes_peace
    (deal base warCost v1 v2 : Nat) (h : v1 ≤ v2)
    (hpeace : peacemaking deal base v1 warCost) :
    peacemaking deal base v2 warCost := by
  unfold peacemaking at *
  -- walkawayValue base v2 ≤ walkawayValue base v1 ≤ deal
  exact Nat.le_trans (walkaway_falls_with_violence base warCost v1 v2 h) hpeace

/-! ## 4. The converse edge: a safe walkaway resists peace -/

/-- **A safe walkaway is worth its full base.** With `violence = 0` there is no
    expected war cost to subtract, so the walkaway value is exactly `base`. When
    walking away is safe, the outside option keeps its whole paper value. -/
theorem safe_walkaway_value (base warCost : Nat) :
    walkawayValue base 0 warCost = base := by
  unfold walkawayValue
  -- 0 * warCost = 0, 0 / 100 = 0, base - 0 = base
  rw [Nat.zero_mul, Nat.zero_div, Nat.sub_zero]

/-- **A safe walkaway resists peace.** When `violence = 0` the walkaway is worth
    the full `base`, so a deal keeps the peace **iff** it is worth at least
    `base`: only deals `≥ base` survive. Peace is hardest precisely when walking
    away is safe — with no threat of war degrading the alternative, parties hold
    out for full value. The exact converse of `war_makes_peace`: remove the
    threat and the bar snaps back up to its maximum. -/
theorem safe_walkaway_resists_peace (deal base warCost : Nat) :
    peacemaking deal base 0 warCost ↔ base ≤ deal := by
  unfold peacemaking
  rw [safe_walkaway_value base warCost]

/-! ## 5. Total war forces peace -/

/-- **Total war zeroes the walkaway.** At maximal violence (`violence = 100`)
    with war cost at least the base (`base ≤ warCost`), the expected war cost
    `(100 * warCost) / 100 = warCost ≥ base` swamps the base, so truncated
    subtraction floors the walkaway value at `0`. There is nothing left to walk
    away to. -/
theorem total_war_zeroes_walkaway (base warCost : Nat) (h : base ≤ warCost) :
    walkawayValue base 100 warCost = 0 := by
  unfold walkawayValue
  -- 100 * warCost / 100 = warCost
  have h100 : 100 * warCost / 100 = warCost := by
    rw [Nat.mul_comm 100 warCost]
    exact Nat.mul_div_cancel warCost (by exact Nat.succ_pos 99)
  rw [h100]
  -- base - warCost = 0 since base ≤ warCost
  exact Nat.sub_eq_zero_of_le h

/-- **Total war forces peace.** At `violence = 100` with `base ≤ warCost`, the
    walkaway is worth `0`, so **every** non-negative deal clears the bar: peace
    is universally acceptable. When the only alternative is annihilation, any
    settlement at all is preferable to fighting. The maximal-deterrence limit of
    `war_makes_peace`: push the threat to the top and the acceptable set becomes
    everything. -/
theorem total_war_forces_peace (deal base warCost : Nat) (h : base ≤ warCost) :
    peacemaking deal base 100 warCost := by
  unfold peacemaking
  rw [total_war_zeroes_walkaway base warCost h]
  -- 0 ≤ deal
  exact Nat.zero_le deal

/-! ## 6. Tie to the Red Queen: the threat, not the war, makes the peace -/

/-- **Over-pushing is pyrrhic — so it is the threat, not the war, that pays.**
    Importing the Red Queen's `over_push_is_pyrrhic`: if conflict pressure `p`
    is pushed past the opponent's grit, the prey hits `0` *and the predator's own
    food collapses to `0`* — both sides lose. Executing total war is
    self-defeating (`predatorFood grit p = 0`).

    Yet `total_war_forces_peace` shows the *threat* of total war (with the
    walkaway zeroed) makes **every** deal peace-acceptable. Bundled, the two say:
    the payoff of war is in its credible threat held at the boundary, never in
    its execution. Escalate to the brink to lower the other side's reservation
    price; cross the brink and you starve on the corpses. Deterrence is the
    threat priced in, the war forever deferred. -/
theorem threat_not_war_makes_peace
    (deal base warCost : Nat) (hbw : base ≤ warCost)
    (grit p : Nat) (hpush : grit < p) :
    -- The threat (total-war limit) makes every deal acceptable …
    peacemaking deal base 100 warCost ∧
    -- … but executing the over-push destroys the aggressor's own gains.
    predatorFood grit p = 0 := by
  refine ⟨total_war_forces_peace deal base warCost hbw, ?_⟩
  exact over_push_is_pyrrhic grit p hpush

/-! ## 7. The deterrence principle (synthesis) -/

/-- **The deterrence principle.** The contrarian core, bundled as one theorem:

    1. **A graver threat lowers the reservation price**
       (`walkaway_falls_with_violence`): `v1 ≤ v2` makes the walkaway worth
       *less*, because the expected cost of violence eats into it.
    2. **War makes peace** (`war_makes_peace`): consequently any deal that held
       the peace under a milder threat still holds it under a graver one — the
       acceptable set only grows as war looms.
    3. **Total war forces peace** (`total_war_forces_peace`): at the limit, with
       the walkaway zeroed, *every* deal is acceptable.

    The threat of war manufactures peace; the closer war, the more peace clears.
    (And by `threat_not_war_makes_peace`, it must stay a threat — executing it is
    pyrrhic.) -/
theorem deterrence_principle
    (deal base warCost v1 v2 : Nat) (hv : v1 ≤ v2) (hbw : base ≤ warCost)
    (hpeace : peacemaking deal base v1 warCost) :
    -- 1. graver threat ⇒ lower reservation price
    (walkawayValue base v2 warCost ≤ walkawayValue base v1 warCost) ∧
    -- 2. war makes peace: the milder-threat deal still holds under the graver one
    (peacemaking deal base v2 warCost) ∧
    -- 3. total war forces peace: every deal clears the bar at the limit
    (peacemaking deal base 100 warCost) := by
  refine ⟨walkaway_falls_with_violence base warCost v1 v2 hv, ?_, ?_⟩
  · exact war_makes_peace deal base warCost v1 v2 hv hpeace
  · exact total_war_forces_peace deal base warCost hbw

end Gnosis.Body.WarMakesPeace
