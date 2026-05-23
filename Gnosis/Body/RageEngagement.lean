import Init
import Gnosis.Body.Robustness
import Gnosis.Body.SapolskyStress

/-!
# Rage Engagement — Outrage Maximizes Engagement, so the Attention Economy Selects for Rage

**Thesis.** Rage/outrage is the most engaging emotional charge content can carry.
An attention economy (social media) whose feed-ranking objective is *engagement*
therefore selects for rage: among items of equal informational signal, the one
carrying more rage scores higher and is promoted. But each promoted rage-unit
extracts attention from the shared **attention commons** and adds to societal
**polarization**. Past the commons' regeneration the commons collapses
(`Robustness.breaks`) — the feed eats the very attention it feeds on. This is the
modern vampire's feeding mechanism: it manufactures rage to harvest attention,
and the harvest is parasitic on a finite host.

This module is the engagement-economy half of the predation arc. It bridges to:

* `Gnosis/Body/Vampire.lean` — the modern vampire feeds by extraction from a host
  commons; rage is its feeding *mechanism*. (Cited, **not imported**: that module
  is being written concurrently and may not yet exist. We re-derive the
  drain/commons/threshold notions locally here so this file stands alone.)
* `Gnosis/ModernArchonDeficit.lean` — the established polarization predicate
  `ModernArchonDeficit.isPolarized` (two versions that cancel yet leave the debt
  in the manifold), the social-media `algorithm` as the optimized IVR whipsaw
  (`ModernArchonDeficit.algorithm_is_ivr`), and AI `phantasmalNoise`. (Cited,
  **not imported**: that module uses `Float`/Mathlib-style predicates.) Rage is
  the driver of the polarization that module names.
* `Gnosis/Body/Robustness.lean` — `breaks`/`withstands`/`grit` give the attention
  commons its collapse threshold (imported, Init-clean).
* `Gnosis/Body/SapolskyStress.lean` — `allostaticLoad` is the structural twin of
  `commonsDrain` (linear cumulative wear crossing a fixed wall); over-extraction
  here mirrors chronic load there (imported, Init-clean).
* `Gnosis/Body/RedQueen.lean` — `over_push_is_pyrrhic`: escalation past grit
  starves the escalator. Our `outrage_is_pyrrhic` is the engagement-economy
  instance of that cliff. (Cited in spirit.)

The arc, as theorems:

1. **Rage raises engagement** (`rage_raises_engagement`): `engagement r s = r + s`
   is monotone in rage — more rage, more engagement, on top of any signal.
2. **The engagement maximizer selects rage** (`engagement_maximizer_selects_rage`):
   among equal-signal items, ranking by engagement promotes the higher-rage item.
3. **Rage drains the commons** (`rage_drains_the_commons`): total attention drain
   `commonsDrain perRage rage = perRage * rage` is monotone in promoted rage, and
   past the commons' regeneration grit the commons `breaks`.
4. **Rage polarizes** (`rage_polarizes`): promoted rage monotonically raises
   polarization (driving `ModernArchonDeficit.isPolarized`).
5. **Outrage is pyrrhic** (`outrage_is_pyrrhic`): maximizing engagement via rage
   past the commons capacity collapses the surviving attention to `0` — the feed
   eats its host (mirrors `RedQueen.over_push_is_pyrrhic`).
6. **Attention hygiene bounds it** (`attention_hygiene_bounds_it`): a cap on
   promoted rage (regulation / non-engagement ranking) keeps drain within the
   commons' regeneration — the commons `withstands`. The fix bounds the objective.
7. `rage_culture_drains_society` — the headline composition.

Rustic Church: `import Init` only (plus the two Init-clean sibling Body modules
`Robustness` and `SapolskyStress`). `Nat` only — no `Float`/`Real`/Mathlib. No
`sorry`; no `simp`/`decide`/`omega` on open goals. Proofs are term-mode and named
core `Nat` lemmas.
-/

namespace Gnosis.Body.RageEngagement

open Gnosis.Body.Robustness

/-! ## 1. Rage raises engagement

Empirically, outrage is the most shareable charge: it travels faster and farther
than joy, sadness, or neutral information. We model engagement on an item as its
informational `signal` plus the `rage` it carries — rage adds engagement on top
of the signal rather than replacing it. -/

/-- **Engagement.** The total engagement an item earns: its informational
    `signal` plus the `rage` it provokes. Rage is additive engagement — outrage
    bait still travels even with little real signal. -/
def engagement (rage signal : Nat) : Nat := rage + signal

/-- **More rage, more engagement (monotone).** Holding informational signal
    fixed, raising the rage charge never lowers engagement and generally raises
    it. This is the empirical fact that the rest of the module turns into a
    selection pressure. -/
theorem rage_raises_engagement (r1 r2 signal : Nat) (h : r1 ≤ r2) :
    engagement r1 signal ≤ engagement r2 signal := by
  unfold engagement
  -- r1 + signal ≤ r2 + signal from r1 ≤ r2.
  exact Nat.add_le_add_right h signal

/-- **Engagement strictly rises with rage when signal is held fixed.** One more
    unit of rage strictly increases engagement: the gradient the optimizer
    climbs is never flat in the rage direction. -/
theorem more_rage_strictly_more_engagement (rage signal : Nat) :
    engagement rage signal < engagement (rage + 1) signal := by
  unfold engagement
  -- rage + signal < (rage + 1) + signal.
  have hbase : rage < rage + 1 := Nat.lt_succ_self rage
  exact Nat.add_lt_add_right hbase signal

/-! ## 2. The engagement maximizer selects rage

A feed that ranks content by engagement is an optimizer over the engagement
objective. With informational signal held equal, the rank order is determined
entirely by rage — so the optimizer's choice *is* "pick the angrier item". -/

/-- The feed *promotes* item `a` over item `b` when `a` earns at least as much
    engagement. (An engagement-ranking feed shows higher-engagement items first.) -/
def promotes (rageA signalA rageB signalB : Nat) : Prop :=
  engagement rageB signalB ≤ engagement rageA signalA

/-- **The engagement maximizer selects rage.** Among two items of *equal*
    informational signal, the engagement-ranking feed promotes the higher-rage
    one. The selection pressure is exact: with signal factored out, ranking by
    engagement *is* ranking by rage. An engagement-maximizing attention economy
    therefore systematically surfaces outrage. -/
theorem engagement_maximizer_selects_rage (r1 r2 signal : Nat) (h : r1 ≤ r2) :
    engagement r1 signal ≤ engagement r2 signal
      ∧ promotes r2 signal r1 signal := by
  refine ⟨rage_raises_engagement r1 r2 signal h, ?_⟩
  -- promotes r2 signal r1 signal  unfolds to  engagement r1 signal ≤ engagement r2 signal.
  unfold promotes
  exact rage_raises_engagement r1 r2 signal h

/-! ## 3. Rage drains the attention commons

The **attention commons** is the shared, finite pool of human attention. Each
unit of promoted rage extracts `perRage` from it (rage is cognitively costly:
it hijacks attention, crowds out reflection). Total drain is linear in promoted
rage — structurally the twin of `SapolskyStress.allostaticLoad` (cumulative wear)
and `Vampire`'s extraction. The commons has a regeneration capacity, its **grit**;
drain beyond it makes the commons `Robustness.breaks`. -/

/-- **Attention-commons drain.** A per-rage extraction `perRage` applied across
    `rage` units of promoted rage accumulates linearly. (Mirrors
    `SapolskyStress.allostaticLoad perTick ticks = perTick * ticks` and the
    extraction Vampire feeds on.) -/
def commonsDrain (perRage rage : Nat) : Nat := perRage * rage

/-- The attention commons' **regeneration grit**: the largest total drain the
    commons can replenish per cycle before it is depleted. (This is
    `Robustness.grit` applied to the commons — the same hard wall.) -/
def commonsGrit (regeneration : Nat) : Nat := regeneration

/-- **Drain is monotone in promoted rage.** Promoting more rage never drains less
    attention — the extraction grows with the harvest. -/
theorem drain_monotone_in_rage (perRage r1 r2 : Nat) (h : r1 ≤ r2) :
    commonsDrain perRage r1 ≤ commonsDrain perRage r2 := by
  unfold commonsDrain
  -- perRage * r1 ≤ perRage * r2 from r1 ≤ r2.
  exact Nat.mul_le_mul_left perRage h

/-- **Rage drains the commons (and past regeneration it breaks).** Two halves of
    the same fact:

    * drain is monotone in promoted rage (`drain_monotone_in_rage`); and
    * for any fixed nonzero per-rage extraction and any regeneration grit, there
      is an amount of promoted rage whose drain exceeds the grit — the attention
      commons then `Robustness.breaks`. The witness is `regeneration + 1` units:
      even the gentlest nonzero extraction, promoted hard enough, crosses every
      fixed regeneration wall. (Structural twin of
      `SapolskyStress.chronic_load_breaks`.) -/
theorem rage_drains_the_commons (perRage r1 r2 regeneration : Nat)
    (hr : r1 ≤ r2) (hp : 0 < perRage) :
    commonsDrain perRage r1 ≤ commonsDrain perRage r2
      ∧ ∃ rage : Nat, breaks (commonsGrit regeneration) (commonsDrain perRage rage) := by
  refine ⟨drain_monotone_in_rage perRage r1 r2 hr, ?_⟩
  refine ⟨regeneration + 1, ?_⟩
  unfold breaks commonsGrit commonsDrain
  -- regeneration < perRage * (regeneration + 1).
  -- Since 1 ≤ perRage we have (regeneration + 1) ≤ perRage * (regeneration + 1).
  have hstep : (regeneration + 1) * 1 ≤ (regeneration + 1) * perRage :=
    Nat.mul_le_mul_left (regeneration + 1) hp
  rw [Nat.mul_one] at hstep
  rw [Nat.mul_comm (regeneration + 1) perRage] at hstep
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self regeneration) hstep

/-! ## 4. Rage polarizes

Beyond draining attention, promoted rage *splits* the audience: outrage sorts
people into opposed camps. We model the polarization a feed accumulates as linear
in promoted rage — each rage-unit adds `perRage` to the polarization index. This
is what drives `ModernArchonDeficit.isPolarized`: two versions that cancel
(`v1 + v2 = 0`) yet leave the debt in the manifold — the binary debt of
inter-version refusal, here *manufactured* by the rage feed. -/

/-- **Polarization** accumulated by the feed: each unit of promoted rage adds
    `perRage` to the polarization index. (Drives `ModernArchonDeficit.isPolarized`,
    the binary-debt predicate.) -/
def polarization (perRage rage : Nat) : Nat := perRage * rage

/-- **Rage polarizes (monotone).** Promoting more rage never lowers polarization
    and generally raises it: the engagement-maximizing feed manufactures the very
    division `ModernArchonDeficit.isPolarized` names. -/
theorem rage_polarizes (perRage r1 r2 : Nat) (h : r1 ≤ r2) :
    polarization perRage r1 ≤ polarization perRage r2 := by
  unfold polarization
  exact Nat.mul_le_mul_left perRage h

/-- **Polarization strictly rises with each promoted rage-unit** (for a nonzero
    per-rage coefficient): the feed cannot promote rage without deepening the
    split — there is no "harmless" extra outrage. -/
theorem each_rage_unit_deepens_split (perRage rage : Nat) (hp : 0 < perRage) :
    polarization perRage rage < polarization perRage (rage + 1) := by
  unfold polarization
  -- perRage * rage < perRage * (rage + 1) since perRage > 0.
  rw [Nat.mul_succ]
  -- goal: perRage * rage < perRage * rage + perRage.
  exact Nat.lt_add_of_pos_right hp

/-! ## 5. Outrage is pyrrhic — the feed eats its host

The attention the commons can still supply, after a drain, is its regeneration
grit minus the drain (truncated at `0`). Maximizing engagement via rage past the
commons' capacity drives that surviving attention to `0`: the feed eats the very
attention it feeds on. This is `RedQueen.over_push_is_pyrrhic` in the
engagement-economy register, and `Vampire`'s parasite-kills-host. -/

/-- **Surviving attention.** What the commons can still supply after a drain: its
    regeneration grit net of the drain, truncated at `0` (once over-extracted,
    nothing is left). -/
def survivingAttention (regeneration drain : Nat) : Nat := regeneration - drain

/-- **Over-drain empties the commons.** When drain strictly exceeds the
    regeneration grit, surviving attention is exactly `0`. Truncated `Nat.sub`
    gives the collapse for free. -/
theorem over_drain_empties (regeneration drain : Nat) (h : regeneration < drain) :
    survivingAttention regeneration drain = 0 := by
  unfold survivingAttention
  exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

/-- **Outrage is pyrrhic.** If the engagement-maximizing feed drains the attention
    commons past its regeneration grit, the surviving attention — the resource the
    feed lives on — collapses to `0`. Maximal rage-harvesting is self-defeating:
    the feed eats its host. This is the engagement-economy instance of
    `RedQueen.over_push_is_pyrrhic` (push past grit and the predator starves) and
    `Vampire`'s parasite that kills what it feeds on. The lesson: drain must stay
    within regeneration, which §6 enforces by *bounding the engagement objective*. -/
theorem outrage_is_pyrrhic (perRage rage regeneration : Nat)
    (h : commonsGrit regeneration < commonsDrain perRage rage) :
    survivingAttention regeneration (commonsDrain perRage rage) = 0 := by
  unfold commonsGrit at h
  exact over_drain_empties regeneration (commonsDrain perRage rage) h

/-- Conversely, when drain stays strictly within regeneration, surviving
    attention is positive: the sustainable regime where the commons persists. -/
theorem sustainable_within_regeneration (perRage rage regeneration : Nat)
    (h : commonsDrain perRage rage < regeneration) :
    0 < survivingAttention regeneration (commonsDrain perRage rage) := by
  unfold survivingAttention
  exact Nat.zero_lt_sub_of_lt h

/-! ## 6. Attention hygiene bounds it — bounding the objective is the fix

The fix is not to ban rage but to *cap* the engagement objective: a non-engagement
ranking, regulation, or personal attention hygiene that limits how much rage the
feed may promote. If promoted rage is capped at a level whose worst-case drain is
within the commons' regeneration, the commons `withstands`. The cure operates on
the objective, not on the content. -/

/-- **A rage cap suffices when its drain is within regeneration.** Attention
    hygiene = capping promoted rage at `cap`. If the cap's drain
    `commonsDrain perRage cap` is within the commons' regeneration grit
    (`hcap`), then *any* promoted rage at or below the cap drains within
    regeneration, so the commons `Robustness.withstands` it. Bounding the
    engagement objective restores resilience. -/
theorem attention_hygiene_bounds_it (perRage cap rage regeneration : Nat)
    (hcap : commonsDrain perRage cap ≤ commonsGrit regeneration)
    (hbounded : rage ≤ cap) :
    withstands (commonsGrit regeneration) (commonsDrain perRage rage) := by
  unfold withstands
  -- drain at `rage` ≤ drain at `cap` ≤ regeneration grit.
  have hmono : commonsDrain perRage rage ≤ commonsDrain perRage cap :=
    drain_monotone_in_rage perRage rage cap hbounded
  unfold commonsGrit at hcap ⊢
  exact Nat.le_trans hmono hcap

/-- **The cap also keeps surviving attention alive.** Under a cap whose drain is
    *strictly* within regeneration, surviving attention is positive for any
    promoted rage at or below the cap — the commons not only survives but retains
    headroom. The bounded objective is genuinely sustainable, not merely
    non-fatal. -/
theorem capped_keeps_attention_alive (perRage cap rage regeneration : Nat)
    (hcap : commonsDrain perRage cap < regeneration)
    (hbounded : rage ≤ cap) :
    0 < survivingAttention regeneration (commonsDrain perRage rage) := by
  have hmono : commonsDrain perRage rage ≤ commonsDrain perRage cap :=
    drain_monotone_in_rage perRage rage cap hbounded
  exact sustainable_within_regeneration perRage rage regeneration
    (Nat.lt_of_le_of_lt hmono hcap)

/-! ## 7. The headline synthesis -/

/-- **Rage culture drains society.** The engagement-maximizing attention economy
    has the structure of a parasite on the attention commons. In one proved
    theorem:

    1. **Selection** — among equal-signal items the engagement feed promotes the
       higher-rage one (`engagement_maximizer_selects_rage`): the objective
       *selects for* rage.
    2. **Drain** — promoted rage drains the attention commons monotonically, and
       past the commons' regeneration grit the commons `Robustness.breaks`
       (`rage_drains_the_commons`).
    3. **Polarization** — promoted rage monotonically raises polarization
       (`rage_polarizes`), driving `ModernArchonDeficit.isPolarized`.
    4. **Pyrrhic** — unchecked, over-draining collapses the surviving attention to
       `0` (`outrage_is_pyrrhic`): the feed eats its host (cf.
       `RedQueen.over_push_is_pyrrhic`, `Vampire`).
    5. **Cure** — capping promoted rage (attention hygiene / regulation / a
       non-engagement ranking) keeps drain within regeneration, so the commons
       `Robustness.withstands` (`attention_hygiene_bounds_it`): the fix is
       bounding the engagement objective.

    This *maps to* the modern vampire's feeding mechanism (rage is the lure,
    attention is the blood) and *has the structure of* an over-extracted commons —
    we do not claim social media literally *is* a vampire; we prove the dynamics
    coincide. -/
theorem rage_culture_drains_society
    (r1 r2 signal perRage cap regeneration : Nat)
    (hrank : r1 ≤ r2) (hp : 0 < perRage)
    (hcap : commonsDrain perRage cap ≤ commonsGrit regeneration) :
    -- 1. Selection: equal-signal ranking promotes the higher-rage item.
    (engagement r1 signal ≤ engagement r2 signal ∧ promotes r2 signal r1 signal) ∧
    -- 2. Drain: monotone, and past regeneration the commons breaks.
    (commonsDrain perRage r1 ≤ commonsDrain perRage r2 ∧
      ∃ rage : Nat, breaks (commonsGrit regeneration) (commonsDrain perRage rage)) ∧
    -- 3. Polarization rises with promoted rage.
    (polarization perRage r1 ≤ polarization perRage r2) ∧
    -- 4. Pyrrhic: over-draining empties the surviving attention.
    (∀ rage : Nat, commonsGrit regeneration < commonsDrain perRage rage →
      survivingAttention regeneration (commonsDrain perRage rage) = 0) ∧
    -- 5. Cure: a rage cap within regeneration keeps the commons withstanding.
    (∀ rage : Nat, rage ≤ cap →
      withstands (commonsGrit regeneration) (commonsDrain perRage rage)) := by
  refine ⟨engagement_maximizer_selects_rage r1 r2 signal hrank,
          rage_drains_the_commons perRage r1 r2 regeneration hrank hp,
          rage_polarizes perRage r1 r2 hrank, ?_, ?_⟩
  · intro rage h
    exact outrage_is_pyrrhic perRage rage regeneration h
  · intro rage hbounded
    exact attention_hygiene_bounds_it perRage cap rage regeneration hcap hbounded

end Gnosis.Body.RageEngagement
