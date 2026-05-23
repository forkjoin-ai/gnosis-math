import Init
import Gnosis.Body.Robustness
import Gnosis.Body.RedQueen

/-!
# The Vampire — Parasitic Drain on a Commons

The folkloric vampire is not, formally, a *monster* in the sense of a single
predator that hunts and is hunted (that is the Red Queen's predator–prey
oscillation). It is a **parasite on a commons**: an entity that extracts a shared
resource — life, blood, attention — *without contributing*, a negative-sum drain
on a pool that everyone draws from. The blood it takes is gone from the village;
nothing flows back.

The decisive feature of a commons is that it **regenerates**: the village births
new life, the herd breeds, attention recovers with rest. A commons can therefore
*tolerate some parasitism* — below a threshold density of vampires the regrowth
outpaces the drain and the pool replenishes (it is **resilient**). Above that
threshold the drain outruns regrowth and the commons **collapses** — drained
faster than it can heal. The folklore knows this exactly: one vampire haunts a
village for generations; a village that becomes *all* vampires has no one left to
feed on and dies (the parasite that kills its host starves — see
`RedQueen.over_push_is_pyrrhic`).

This module formalizes that arc in `Nat`:

* A commons has regeneration `regen` per tick; `n` vampires each drain `drain`
  per tick; the commons is **sustained** iff `n * drain ≤ regen` and
  **collapsing** iff `regen < n * drain`.
* `vampireGrit regen drain := regen / drain` is the commons' **grit** against
  parasites: the maximum sustainable vampire density. Below it the commons is
  sustained (`few_vampires_sustained`); the grit is finite and positive
  (`commons_grit_is_finite`) — a commons tolerates *some*, not unbounded,
  parasitism.
* Past the grit the commons `breaks` (`too_many_vampires_collapse`), bridging to
  `Robustness.breaks`: drain exceeds the commons' regenerative tolerance.
* A vampire population that drains the commons to zero then has nothing left to
  drain (`total_drain_is_pyrrhic`), bridging to `RedQueen.over_push_is_pyrrhic`:
  the parasite that kills the host starves.

## The modern vampire: the attention economy

The cellphone / engagement economy has the *same structure* with collective
attention as the commons. Engagement-harvesting platforms extract attention from
a shared pool without returning rest; below a threshold the attention commons
recovers, above it collective attention collapses (chronic distraction, fragmented
focus). This module's `attention_economy_is_a_vampire` maps the drain model onto
that commons. The supporting attention machinery lives in (cited, not imported —
they are not `Init`-clean):

* `Gnosis.KarmicAttentionOptimizer` — heads whose `(L, F)` drift off the Pell
  manifold are pruned; an attention regulator. The harvested signal is `wasteQ` /
  `opportunityK` mass extracted per step.
* `Gnosis.EnvironmentalAttention` — salience / persistence allocation across a
  sensory commons; what an engagement economy competes to capture.
* `Gnosis.AttentionScalingLaw` — the per-swerve clinamen cost of an attention
  step (`buleyUnitScore +1` per lift); the *price* of each unit drained from the
  attention commons, and the budget that bounds it.

Per repo policy the corollary says the attention economy *has the structure of /
maps to* the vampire model — not that it *is* one; the identity is the shared
threshold dynamics, made precise below.

Rustic Church: `Init` only (plus the `Init`-clean siblings `Robustness` and
`RedQueen`). `Nat` arithmetic; proofs from core `Nat` lemmas
(`Nat.le_div_iff_mul_le`, `Nat.div_le_self`, `Nat.div_lt_iff_lt_mul`,
`Nat.lt_irrefl`, `Nat.lt_of_lt_of_le`, `Nat.le_trans`, `Nat.sub_eq_zero_of_le`).
No `sorry`; no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.Vampire

open Gnosis.Body.Robustness
open Gnosis.Body.RedQueen

/-! ## 1. The commons and its drain -/

/-- Total drain on the commons per tick: `n` vampires each taking `drain`. The
    parasites do not contribute, so this is pure extraction — a negative-sum
    withdrawal from the shared pool. -/
def totalDrain (n drain : Nat) : Nat := n * drain

/-- **Net commons change per tick, signed.** Regeneration in, total drain out.
    When the drain exceeds regeneration the net is negative — the pool shrinks.
    (`Int` is genuine here: the commons can be running down, not merely at rest.) -/
def netCommons (regen n drain : Nat) : Int :=
  (regen : Int) - (totalDrain n drain : Int)

/-- The commons is **sustained** iff the per-tick drain stays within regeneration:
    the pool replenishes at least as fast as the vampires bleed it. -/
def sustained (regen n drain : Nat) : Prop := n * drain ≤ regen

/-- The commons is **collapsing** iff the per-tick drain strictly exceeds
    regeneration: the pool is bled faster than it heals. -/
def collapsing (regen n drain : Nat) : Prop := regen < n * drain

/-- **Sustained and collapsing are exhaustive and exclusive.** Against a given
    parasite load the commons either holds (regrowth covers the drain) or
    collapses (drain outruns regrowth) — no third option, and never both. The
    commons-level reading of `Robustness.robustness_trichotomy`. -/
theorem commons_dichotomy (regen n drain : Nat) :
    sustained regen n drain ∨ collapsing regen n drain := by
  unfold sustained collapsing
  rcases Nat.lt_or_ge regen (n * drain) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- A sustained commons is not also collapsing: replenishment and collapse are
    genuine opposites, not a matter of degree. -/
theorem sustained_excludes_collapsing (regen n drain : Nat)
    (hs : sustained regen n drain) : ¬ collapsing regen n drain := by
  unfold sustained at hs
  unfold collapsing
  intro hc
  exact Nat.lt_irrefl regen (Nat.lt_of_lt_of_le hc hs)

/-- **Net change is nonnegative exactly when sustained.** The signed `netCommons`
    is `≥ 0` iff the drain is within regeneration — tying the `Int` ledger to the
    `Nat` threshold so the two readings agree. -/
theorem netCommons_nonneg_iff_sustained (regen n drain : Nat) :
    0 ≤ netCommons regen n drain ↔ sustained regen n drain := by
  unfold netCommons totalDrain sustained
  constructor
  · intro h
    -- 0 ≤ regen - (n*drain) ⟹ n*drain ≤ regen (in Int), then cast back to Nat.
    have hle : ((n * drain : Nat) : Int) ≤ (regen : Int) := by
      exact Int.le_of_sub_nonneg h
    exact Int.ofNat_le.mp hle
  · intro h
    have hle : ((n * drain : Nat) : Int) ≤ (regen : Int) := Int.ofNat_le.mpr h
    exact Int.sub_nonneg_of_le hle

/-! ## 2. The commons' grit against parasites -/

/-- **The commons' grit against parasites:** the maximum sustainable vampire
    density, the integer quotient `regen / drain`. One vampire more than this
    crosses the regeneration wall (cf. `Allostasis.allostaticGrit`,
    `RedQueen.preyGrit`). A commons can carry *some* parasites; this is how many. -/
def vampireGrit (regen drain : Nat) : Nat := regen / drain

/-- **(THM 1) Few vampires: the commons is sustained.** Below the commons' grit
    (`n ≤ vampireGrit regen drain`) the total drain stays within regeneration, so
    the commons is `sustained` — the pool replenishes faster than the vampires
    bleed it. This is the commons' grit *working*: it absorbs parasitism up to its
    threshold. Proved from `Nat.le_div_iff_mul_le` (for `0 < drain`). -/
theorem few_vampires_sustained (regen n drain : Nat) (hd : 0 < drain)
    (h : n ≤ vampireGrit regen drain) : sustained regen n drain := by
  unfold vampireGrit at h
  unfold sustained
  -- n ≤ regen / drain  ↔  n * drain ≤ regen   (for drain > 0)
  exact (Nat.le_div_iff_mul_le hd).mp h

/-- The drain at exactly the grit density is still within regeneration: the
    commons endures right up to its threshold (the boundary case of THM 1). -/
theorem grit_density_sustained (regen drain : Nat) (hd : 0 < drain) :
    sustained regen (vampireGrit regen drain) drain :=
  few_vampires_sustained regen (vampireGrit regen drain) drain hd (Nat.le_refl _)

/-! ## 3. Past the threshold the commons collapses (bridge to `Robustness.breaks`) -/

/-- The single arithmetic fact behind collapse: for `drain > 0`, one vampire past
    the grit (`vampireGrit + 1`) drains strictly more than regeneration. One
    parasite past the quotient floor, the extraction has crossed the wall. Mirrors
    `Allostasis.load_at_witness_exceeds`. -/
theorem drain_at_grit_succ_exceeds (regen drain : Nat) (hd : 0 < drain) :
    regen < (vampireGrit regen drain + 1) * drain := by
  unfold vampireGrit
  -- div_lt_iff_lt_mul : x / k < y ↔ x < y * k   (for k > 0)
  have hstep : regen / drain < regen / drain + 1 := Nat.lt_succ_self _
  exact (Nat.div_lt_iff_lt_mul hd).mp hstep

/-- **(THM 2) Too many vampires: the commons collapses.** Strictly above the
    commons' grit the total drain exceeds regeneration, so the commons is
    `collapsing`; equivalently it `breaks` in the sense of `Robustness.breaks` —
    the parasite load exceeds the commons' regenerative tolerance. The threshold
    is sharp: at `vampireGrit + 1` parasites the pool is bled faster than it heals.
    Here regeneration plays the rôle of `Robustness` tolerance and the total drain
    the rôle of the perturbation. -/
theorem too_many_vampires_collapse (regen drain : Nat) (hd : 0 < drain) :
    collapsing regen (vampireGrit regen drain + 1) drain ∧
    breaks regen (totalDrain (vampireGrit regen drain + 1) drain) := by
  have hexceed : regen < (vampireGrit regen drain + 1) * drain :=
    drain_at_grit_succ_exceeds regen drain hd
  refine ⟨hexceed, ?_⟩
  -- breaks regen (totalDrain ...) is definitionally regen < (...)*drain.
  unfold breaks totalDrain
  exact hexceed

/-- **General collapse implies breaking.** For *any* parasite load that makes the
    commons `collapsing`, the drain `breaks` the commons' regenerative tolerance.
    The bridge is definitional but load-bearing: `collapsing` *is* the commons-
    level instance of `Robustness.breaks`. -/
theorem collapsing_breaks (regen n drain : Nat)
    (h : collapsing regen n drain) : breaks regen (totalDrain n drain) := by
  unfold collapsing at h
  unfold breaks totalDrain
  exact h

/-! ## 4. The commons' grit is finite and positive -/

/-- **(THM 3) A commons tolerates SOME parasitism, not unbounded.** For a
    survivable nonzero drain (`0 < drain ≤ regen`) the commons' grit against
    parasites is *finite* — it never exceeds `regen`, so a large enough vampire
    population always collapses it in bounded growth — yet *positive* — the
    commons can carry at least one vampire before it begins to fail. Mirrors
    `Allostasis.allostatic_grit`: bounded resilience, neither zero nor infinite. -/
theorem commons_grit_is_finite (regen drain : Nat) (hd : 0 < drain)
    (hle : drain ≤ regen) :
    0 < vampireGrit regen drain ∧ vampireGrit regen drain ≤ regen := by
  unfold vampireGrit
  refine ⟨?_, Nat.div_le_self regen drain⟩
  -- 0 < regen / drain  ⇐  drain * 1 ≤ regen  ⇐  drain ≤ regen.
  refine (Nat.le_div_iff_mul_le hd).mpr ?_
  rw [Nat.one_mul]
  exact hle

/-! ## 5. Total drain is pyrrhic (bridge to `RedQueen.over_push_is_pyrrhic`) -/

/-- The commons remaining after a population drains it: the regeneration margin if
    the drain is within `regen`, else `0` (the pool is emptied). Truncated
    `Nat.sub` gives exhaustion for free once the drain passes regeneration —
    exactly `RedQueen.preyPopulation` with `regen` as grit and `totalDrain` as
    pressure. -/
def commonsRemaining (regen n drain : Nat) : Nat := regen - totalDrain n drain

/-- The vampires' food supply is whatever of the commons remains. No commons, no
    food (cf. `RedQueen.predatorFood`). -/
def vampireFood (regen n drain : Nat) : Nat := commonsRemaining regen n drain

/-- Past the regeneration wall the remaining commons is exactly `0` — the pool is
    drained dry. Mirrors `RedQueen.prey_extinct_beyond_grit`. -/
theorem commons_emptied_when_collapsing (regen n drain : Nat)
    (h : collapsing regen n drain) : commonsRemaining regen n drain = 0 := by
  unfold commonsRemaining totalDrain
  unfold collapsing at h
  -- regen < n*drain ⟹ regen ≤ n*drain ⟹ regen - n*drain = 0.
  exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

/-- **(THM 4) Total drain is pyrrhic — the parasite that kills the host starves.**
    A vampire population whose total drain empties the commons (`collapsing`)
    leaves nothing left to drain: the vampires' own food supply collapses to `0`.
    The parasite cannot "win" by unbounded extraction; draining the host to death
    starves the parasite.

    This is the *same structure* as `RedQueen.over_push_is_pyrrhic` (over-predation
    starves the predator), instantiated with the commons' regeneration as the grit
    and the total drain as the pressure: when `regen < totalDrain n drain`, the
    `RedQueen` cliff gives `predatorFood regen (totalDrain n drain) = 0`, which is
    exactly `vampireFood regen n drain = 0`. -/
theorem total_drain_is_pyrrhic (regen n drain : Nat)
    (h : collapsing regen n drain) : vampireFood regen n drain = 0 := by
  -- Reduce to the RedQueen cliff with grit := regen, pressure := totalDrain n drain.
  unfold collapsing at h
  have hcliff : RedQueen.predatorFood regen (totalDrain n drain) = 0 :=
    RedQueen.over_push_is_pyrrhic regen (totalDrain n drain) h
  -- predatorFood regen (totalDrain ..) = preyPopulation .. = regen - totalDrain ..
  --                                    = commonsRemaining .. = vampireFood ..
  unfold vampireFood commonsRemaining
  unfold RedQueen.predatorFood RedQueen.preyPopulation at hcliff
  exact hcliff

/-- Conversely, while strictly below the regeneration wall the vampires' food is
    positive: the sustainable regime where both the commons and (a bounded) parasite
    load persist. Mirrors `RedQueen.sustainable_within_grit`. -/
theorem vampires_fed_within_grit (regen n drain : Nat)
    (h : totalDrain n drain < regen) : 0 < vampireFood regen n drain := by
  unfold vampireFood commonsRemaining
  have hcliff : 0 < RedQueen.predatorFood regen (totalDrain n drain) :=
    RedQueen.sustainable_within_grit regen (totalDrain n drain) h
  unfold RedQueen.predatorFood RedQueen.preyPopulation at hcliff
  exact hcliff

/-! ## 6. The modern vampire: the attention economy -/

/-- **(THM 5) The attention economy maps to the vampire model.** Read the commons
    as the collective **attention** pool: `attnRegen` is how fast attention
    recovers per tick (rest, focus restored), `harvesters` is the number of
    engagement-harvesting actors, and `extract` is the attention each pulls per
    tick. The harvesters return nothing to the pool — pure extraction, the modern
    parasite's negative-sum drain (the per-unit price of which is the clinamen cost
    of `Gnosis.AttentionScalingLaw`; the salience it competes for is
    `Gnosis.EnvironmentalAttention`; the drift-pruning regulator is
    `Gnosis.KarmicAttentionOptimizer`).

    The claim is *structural*, not an identity: the attention economy **has the
    structure of** the vampire drain. Concretely, when extraction exceeds
    attention regeneration the collective attention commons is `collapsing` and
    therefore `breaks` — the *same* threshold dynamics, with the *same* sharp grit
    `vampireGrit attnRegen extract`. Below the grit the attention commons is
    sustained; above it, collapse. -/
theorem attention_economy_is_a_vampire
    (attnRegen harvesters extract : Nat) (he : 0 < extract)
    (hover : attnRegen < harvesters * extract) :
    -- below the grit, the attention commons is sustained
    (harvesters ≤ vampireGrit attnRegen extract →
        sustained attnRegen harvesters extract) ∧
    -- above regeneration, the attention commons collapses ...
    collapsing attnRegen harvesters extract ∧
    -- ... and so breaks the attention commons' regenerative tolerance.
    breaks attnRegen (totalDrain harvesters extract) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hbelow
    exact few_vampires_sustained attnRegen harvesters extract he hbelow
  · unfold collapsing
    exact hover
  · exact collapsing_breaks attnRegen harvesters extract hover

/-! ## 7. The headline synthesis -/

/-- **The vampire principle.** The folkloric vampire — and its modern form, the
    attention economy — is a parasitic, negative-sum drain on a commons, and the
    formal arc closes on a single sharp threshold:

    1. **Bounded resilience.** For a survivable nonzero drain (`0 < drain ≤ regen`)
       the commons' grit `vampireGrit regen drain` is finite *and* positive: a
       commons tolerates *some* parasitism — neither none nor unbounded.
    2. **Sustainable only below the grit.** At or below the grit density the total
       drain stays within regeneration, so the commons is `sustained` — the pool
       replenishes faster than the parasites bleed it.
    3. **Collapse beyond the grit.** One vampire past the grit, the drain exceeds
       regeneration: the commons is `collapsing` and `breaks` (the
       `Robustness.breaks` cliff) — drained faster than it heals.
    4. **Self-defeating extraction.** A parasite load that empties the commons
       leaves nothing to feed on: `vampireFood` collapses to `0` — the same
       `RedQueen.over_push_is_pyrrhic` cliff. The parasite that kills the host
       starves.

    Bundled so the four facets are provably one theory: a parasite is sustainable
    only below the commons' grit; beyond it the commons collapses and the
    parasitism is self-defeating; the attention economy has this structure. -/
theorem vampire_principle
    (regen drain : Nat) (hd : 0 < drain) (hle : drain ≤ regen)
    (n : Nat) :
    -- 1. bounded resilience: grit is finite and positive
    (0 < vampireGrit regen drain ∧ vampireGrit regen drain ≤ regen) ∧
    -- 2. sustainable below the grit
    (n ≤ vampireGrit regen drain → sustained regen n drain) ∧
    -- 3. collapse one past the grit: collapsing and breaks
    (collapsing regen (vampireGrit regen drain + 1) drain ∧
      breaks regen (totalDrain (vampireGrit regen drain + 1) drain)) ∧
    -- 4. self-defeating: total drain past regeneration starves the parasite
    (∀ m : Nat, collapsing regen m drain → vampireFood regen m drain = 0) := by
  refine ⟨commons_grit_is_finite regen drain hd hle, ?_, ?_, ?_⟩
  · intro h
    exact few_vampires_sustained regen n drain hd h
  · exact too_many_vampires_collapse regen drain hd
  · intro m hm
    exact total_drain_is_pyrrhic regen m drain hm

end Gnosis.Body.Vampire
