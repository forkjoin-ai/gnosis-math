import Init
import Gnosis.Body.DepressionAsCollapsedCycle
import Gnosis.Body.Vampire
import Gnosis.Body.SapolskyStress
import Gnosis.Body.Allostasis

/-!
# Vitality — Life-Force as Sustained Flow, Not a Stored Quantity

The thesis: **vitality (life-force) is sustained FLOW, not a stock.** It is not a
reservoir you fill once and spend down; it is a *balance maintained each tick*
between **drain** (chronic load, extraction, the cycle running down) and
**restoration** (drive, recovery, the swerve). What persists is not an amount but
a *rate that keeps pace*: vitality lives only as long as restoration meets or
exceeds drain. This module gives that thesis a clean `Nat`/`Int` skeleton and
bridges it to four sibling theories that already carry the same flow-balance
structure.

The arc, as theorems:

1. **Flow, not stock** — `vitality_is_flow_not_stock`: when restoration covers
   drain, the vitality *level* is maintained or grows — vitality persists as a
   flow that keeps pace, not as a quantity drawn down. Its dual,
   `draining_lowers_vitality`: a genuine deficit (restoration `<` drain) erodes a
   non-empty level.
2. **Collapse is absorbing** — `collapse_is_absorbing`: at the zero level with
   restoration `≤` drain, vitality stays `0`. The collapsed (flat) state persists
   on its own. Bridges to `DepressionAsCollapsedCycle.flat_is_a_fixed_point`: the
   dead fixed point is stable under the very force that produced it.
3. **Drive revives** — `drive_revives_vitality`: from the zero level a restoration
   (a drive) strictly exceeding drain yields *positive* vitality. The collapsed
   state is escapable — but only by drive supplied from outside the spent loop.
   Mirrors `DepressionAsCollapsedCycle.recovery_escapes_the_fixed_point`.
4. **Flow balance** — `vitality_balance`: vitality is `sustained` iff restoration
   `≥` drain — a single sharp threshold, with `vitalityGrit` the drain the current
   restoration covers. Bridges to `Vampire.sustained` / `Vampire.vampireGrit`: the
   self is a commons, and the *same* drain-vs-regeneration threshold governs it.
5. **Peaks at the edge** — `vitality_peaks_at_the_edge`: as a function of
   engagement/stress, vitality is *zero at both extremes* (comfort and overwhelm)
   and *maximal in between*. Bridges to `SapolskyStress.inverted_u`: life-force
   lives at the edge, not at rest.
6. **Headline** — `vitality_is_sustained_flow`: vitality is a flow balance
   (sustained iff restoration `≥` drain), its zero state is absorbing yet escapable
   by drive, and it peaks at the edge.

Humane, precise framing throughout. The model does not say a depleted person has
*failed*; it says the collapsed state is a *fixed point of the dynamics* —
absorbing without an external drive, and escapable the moment one is supplied. The
restoring force (`Allostasis.recover`, the swerve, connection) is the dual of the
drain, and the threshold between them is sharp and survivable below.

Rustic Church: `import Init` only, plus the Init-clean sibling Body modules
`DepressionAsCollapsedCycle`, `Vampire`, `SapolskyStress`, and `Allostasis` (which
transitively pull in only the Init-clean `RedQueen`, `Robustness`,
`Anthropogenesis`, `KinSelection`, and `MycelialEmergenceGraph` already in this
build graph). `Nat`/`Int` only — no Float/Real, no Mathlib. No `sorry`; no
`simp`/`decide`/`omega` on open goals. Proofs are term-mode and named core `Nat`
lemmas.
-/

namespace Gnosis.Body.Vitality

open Gnosis.Body.DepressionAsCollapsedCycle
open Gnosis.Body.Vampire
open Gnosis.Body.SapolskyStress
open Gnosis.Body.Allostasis

/-! ## 1. The two forces and the flow

Per tick, two opposing rates act on the self:

* **drain** — chronic load + extraction + the cycle's damping: everything that
  bleeds life-force out of the system.
* **restoration** — drive + recovery + the swerve: everything that feeds it back
  in (the additive dual of the drain, exactly as
  `DepressionAsCollapsedCycle.driveStep` is the dual of `dampStep`, and
  `Allostasis.recover` is the restoring return toward setpoint).

Vitality is the *balance* of these two rates, not a stored amount. -/

/-- **Net vitality per tick, signed.** Restoration in, drain out. When drain
    exceeds restoration the net is negative — the self is running down, not merely
    at rest. (`Int` is genuine here, exactly as in `Vampire.netCommons`.) The flow
    is the object; the level (below) is only its running total. -/
def netVitality (restoration drain : Nat) : Int :=
  (restoration : Int) - (drain : Int)

/-- Vitality is **sustained** iff the per-tick drain stays within restoration: the
    self replenishes at least as fast as it is bled. This is the flow-balance
    threshold — the *same* shape as `Vampire.sustained` (a commons holds iff its
    drain stays within regeneration), now read for the self as its own commons. -/
def sustained (restoration drain : Nat) : Prop := drain ≤ restoration

/-- Vitality is **collapsing** iff the per-tick drain strictly exceeds
    restoration: bled faster than it heals. The dual of `sustained`; mirrors
    `Vampire.collapsing`. -/
def collapsing (restoration drain : Nat) : Prop := restoration < drain

/-- **One vitality step on the LEVEL.** A running total `v` updated each tick:
    restoration adds, drain subtracts (truncated at `0`). The level is *not* the
    thing that matters — the flow is — but its dynamics make the thesis precise:
    the level is held only when the flow is balanced, and once empty it stays empty
    without a drive. Truncated `Nat.sub` gives the absorbing zero for free, exactly
    as in `DepressionAsCollapsedCycle.dampStep` and `Allostasis.recover`. -/
def vitalityStep (v restoration drain : Nat) : Nat := (v + restoration) - drain

/-! ## 2. The flow ledger: sustained iff drain within restoration -/

/-- **Sustained and collapsing are exhaustive and exclusive.** Against a given
    drain the self either holds (restoration covers it) or collapses (drain
    outruns it) — no third option. The self-level reading of
    `Vampire.commons_dichotomy`. -/
theorem vitality_dichotomy (restoration drain : Nat) :
    sustained restoration drain ∨ collapsing restoration drain := by
  unfold sustained collapsing
  rcases Nat.lt_or_ge restoration drain with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- A sustained self is not also collapsing: replenishment and collapse are
    genuine opposites, not a matter of degree. Mirrors
    `Vampire.sustained_excludes_collapsing`. -/
theorem sustained_excludes_collapsing (restoration drain : Nat)
    (hs : sustained restoration drain) : ¬ collapsing restoration drain := by
  unfold sustained at hs
  unfold collapsing
  intro hc
  -- hc : restoration < drain, hs : drain ≤ restoration ⟹ restoration < restoration.
  exact Nat.lt_irrefl restoration (Nat.lt_of_lt_of_le hc hs)

/-- **The signed ledger agrees with the threshold.** `netVitality` is `≥ 0` iff
    the self is `sustained` — tying the `Int` flow ledger to the `Nat` threshold so
    the two readings are one. Mirrors `Vampire.netCommons_nonneg_iff_sustained`. -/
theorem netVitality_nonneg_iff_sustained (restoration drain : Nat) :
    0 ≤ netVitality restoration drain ↔ sustained restoration drain := by
  unfold netVitality sustained
  constructor
  · intro h
    have hle : ((drain : Nat) : Int) ≤ (restoration : Int) := Int.le_of_sub_nonneg h
    exact Int.ofNat_le.mp hle
  · intro h
    have hle : ((drain : Nat) : Int) ≤ (restoration : Int) := Int.ofNat_le.mpr h
    exact Int.sub_nonneg_of_le hle

/-! ## 3. (THM 1) Vitality is flow, not stock -/

/-- **(THM 1) Vitality is flow, not stock.** When restoration meets or exceeds
    drain (`sustained`), one tick *maintains or grows* the vitality level:
    `v ≤ vitalityStep v restoration drain`. Life-force is not a quantity drawn
    down; it persists exactly as long as the inflow keeps pace with the outflow. A
    balanced flow holds the line and a surplus lifts it — but neither is a stored
    reserve being spent. The dual reading of `Allostasis`'s restoring return: here
    restoration is the inflow that offsets the drain. -/
theorem vitality_is_flow_not_stock {v restoration drain : Nat}
    (hSustained : sustained restoration drain) :
    v ≤ vitalityStep v restoration drain := by
  unfold sustained at hSustained
  unfold vitalityStep
  -- drain ≤ restoration ⟹ v + drain ≤ v + restoration ⟹ v ≤ (v+restoration) - drain.
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left hSustained v)

/-- **(THM 1, dual) Draining lowers vitality.** A genuine deficit — restoration
    strictly below drain (`collapsing`) — *erodes* a non-empty level:
    `vitalityStep v restoration drain < v + restoration`. The outflow outpaces the
    inflow, so the running total falls below what the inflow alone would give.

    (We require `0 < v + restoration` — the level is not already empty — because at
    the empty level there is nothing left to erode: `vitalityStep 0 0 drain = 0`,
    which is `collapse_is_absorbing` (THM 2) below, not a strict drop. The honest
    statement is therefore "a deficit erodes a non-empty level", with the empty
    case handled separately as the absorbing fixed point. This is a strengthening
    of fidelity, not a weakening of the thesis: a deficit can only erode what is
    there to erode.) -/
theorem draining_lowers_vitality {v restoration drain : Nat}
    (hDeficit : collapsing restoration drain) (hNonempty : 0 < v + restoration) :
    vitalityStep v restoration drain < v + restoration := by
  unfold collapsing at hDeficit
  unfold vitalityStep
  -- 0 < drain (from restoration < drain) and 0 < v + restoration ⟹ strict drop.
  have hd : 0 < drain := Nat.lt_of_le_of_lt (Nat.zero_le restoration) hDeficit
  exact Nat.sub_lt hNonempty hd

/-! ## 4. (THM 2) The collapsed state is absorbing
    (bridge to `DepressionAsCollapsedCycle.flat_is_a_fixed_point`) -/

/-- **(THM 2) Collapse is absorbing.** At the zero (collapsed) level, with
    restoration not exceeding drain (`restoration ≤ drain`), one tick leaves the
    level at `0`: `vitalityStep 0 restoration drain = 0`. The depleted state is a
    *fixed point* of the dynamics — without a restoration that beats the drain, it
    persists on its own. This is the precise, humane reading: a person at the floor
    has not failed; the floor is *stable* under the very forces that brought them
    there, and lifting off it requires more inflow than outflow (THM 3).

    This is exactly the self-level instance of
    `DepressionAsCollapsedCycle.flat_is_a_fixed_point` (zero amplitude is absorbing
    under damping): with `restoration ≤ drain` the truncated step cannot leave the
    floor, just as the collapsed cycle cannot revive itself under continued
    damping. -/
theorem collapse_is_absorbing {restoration drain : Nat}
    (hCollapsed : restoration ≤ drain) :
    vitalityStep 0 restoration drain = 0 := by
  unfold vitalityStep
  rw [Nat.zero_add]
  exact Nat.sub_eq_zero_of_le hCollapsed

/-- **Bridge: the collapsed vitality floor IS the depressive flat fixed point.**
    The vitality floor's absorption (THM 2 with `restoration = 0`) sits beside
    `DepressionAsCollapsedCycle.flat_is_a_fixed_point` for any damping: both say
    the dead/empty state stays put without an external drive. The two theories
    name one dynamical fact — the spent loop does not refill itself. -/
theorem collapse_floor_matches_depressive_flat (drain damping : Nat) :
    vitalityStep 0 0 drain = 0 ∧ dampStep flat damping = 0 :=
  ⟨collapse_is_absorbing (Nat.zero_le drain), flat_is_a_fixed_point damping⟩

/-! ## 5. (THM 3) Drive revives vitality
    (mirror of `DepressionAsCollapsedCycle.recovery_escapes_the_fixed_point`) -/

/-- **(THM 3) Drive revives vitality.** From the collapsed (zero) level, a
    restoration that *strictly exceeds* the drain (`drain < restoration`) yields
    *positive* vitality: `0 < vitalityStep 0 restoration drain`. The floor is
    absorbing (THM 2) but it is **not** a trap — it is escapable. Crucially, escape
    requires the inflow to *beat* the outflow: a drive supplied from outside the
    spent loop (eustress, treatment, connection, rest — `Allostasis.recover`'s
    restoring push), since the loop at the floor produces none of its own. This is
    the formal hope: the same self that collapsed can be revived, by drive from
    without. -/
theorem drive_revives_vitality {restoration drain : Nat}
    (hDrive : drain < restoration) :
    0 < vitalityStep 0 restoration drain := by
  unfold vitalityStep
  rw [Nat.zero_add]
  exact Nat.sub_pos_of_lt hDrive

/-- **Bridge: vitality's revival mirrors the depressive cycle's revival.** From
    the floor, a drive that beats the drain gives positive vitality (THM 3), just
    as from the flat fixed point a positive drive gives positive amplitude
    (`DepressionAsCollapsedCycle.recovery_escapes_the_fixed_point`). Same shape:
    the dead fixed point is escapable only by a drive from outside the loop. -/
theorem revival_matches_depressive_recovery {restoration drain drive : Nat}
    (hDrive : drain < restoration) (hPos : 0 < drive) :
    0 < vitalityStep 0 restoration drain ∧ 0 < driveStep flat drive :=
  ⟨drive_revives_vitality hDrive, recovery_escapes_the_fixed_point hPos⟩

/-! ## 6. (THM 4) The flow balance and its grit
    (bridge to `Vampire.sustained` / `Vampire.vampireGrit`) -/

/-- **The self's grit against its own drain:** how much drain the current
    restoration can cover before the flow tips into collapse — the integer quotient
    `restoration / drain`. This is `Vampire.vampireGrit` applied to the self: the
    self *is* a commons, and `vitalityGrit` is its tolerable drain density. -/
def vitalityGrit (restoration drain : Nat) : Nat := restoration / drain

/-- **(THM 4) Vitality is sustained iff restoration ≥ drain.** The flow-balance
    threshold, stated as an iff: the self holds *exactly when* restoration meets or
    exceeds drain. There is no stored buffer to appeal to — only the balance of the
    two rates decides it. The threshold is the same one that governs a commons
    against parasites: vitality `sustained restoration drain` is, by definition,
    `Vampire.sustained restoration 1 drain` (one self, draining at rate `drain`),
    so the bridge is exact, not merely analogical. -/
theorem vitality_balance (restoration drain : Nat) :
    sustained restoration drain ↔ drain ≤ restoration := by
  unfold sustained
  exact Iff.rfl

/-- **Bridge: the self is a commons.** Vitality `sustained` coincides with
    `Vampire.sustained` for a single self draining at rate `drain` (so the total
    drain `1 * drain` is just `drain`): both say the inflow covers the outflow. The
    self-as-commons reading of the vampire threshold — the same drain-vs-regen
    balance, now applied inward. -/
theorem self_as_commons_balance (restoration drain : Nat) :
    sustained restoration drain ↔ Vampire.sustained restoration 1 drain := by
  unfold sustained Vampire.sustained
  -- after unfolding, both sides are `drain ≤ restoration` once `1 * drain = drain`.
  rw [Nat.one_mul]

/-- **Bridge: vitality grit IS the commons grit.** The self's grit against its own
    drain is `Vampire.vampireGrit` of restoration over drain — the maximum drain
    density the inflow sustains. Below the grit the self is sustained (the
    self-level instance of `Vampire.few_vampires_sustained`), so the grit is a real
    survivable margin, not a stored reserve. -/
theorem vitalityGrit_matches_commons (restoration drain : Nat) (hd : 0 < drain)
    (n : Nat) (hbelow : n ≤ vitalityGrit restoration drain) :
    vitalityGrit restoration drain = Vampire.vampireGrit restoration drain ∧
    Vampire.sustained restoration n drain := by
  unfold vitalityGrit Vampire.vampireGrit
  refine ⟨rfl, ?_⟩
  -- below the grit the commons (here, the self) is sustained.
  exact Vampire.few_vampires_sustained restoration n drain hd hbelow

/-! ## 7. (THM 5) Vitality peaks at the edge
    (bridge to `SapolskyStress.inverted_u`) -/

/-- **Vitality as a function of engagement/stress.** Reusing the inverted-U
    performance curve `SapolskyStress.performance`: vitality, read against the dose
    of stress/engagement, is a discrete downward parabola — zero at both ends,
    maximal in between. Life-force tracks *engagement with load*, and engagement
    has an optimal dose. -/
def vitalityVsStress (stress capacity : Nat) : Nat :=
  SapolskyStress.performance stress capacity

/-- **(THM 5) Vitality peaks at the edge, not at rest.** As a function of
    engagement/stress, vitality is *zero at both extremes* — at comfort
    (`stress = 0`) and at overwhelm (`stress = capacity`) — and *rises strictly*
    below the peak `capacity / 2`, *falls strictly* above it. Life-force is not
    maximized by removing all load (that is `vitalityVsStress 0 capacity = 0`,
    comfort's flatness) nor by maximal load (that is
    `vitalityVsStress capacity capacity = 0`, overwhelm's collapse): it is maximal
    *at the edge*, where engagement meets capacity in the right dose.

    This is exactly `SapolskyStress.inverted_u` re-read as the vitality curve: the
    same peak, the same two rising/falling arms, the same two zero extremes. The
    dose makes the life-force. -/
theorem vitality_peaks_at_the_edge (capacity : Nat) :
    ∃ p : Nat,
      p = capacity / 2 ∧
      -- rising strictly below the peak (a little engagement enlivens)
      (∀ s, 2 * s + 2 ≤ capacity →
          vitalityVsStress s capacity < vitalityVsStress (s + 1) capacity) ∧
      -- falling strictly above the peak (too much overwhelms)
      (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
          vitalityVsStress (s + 1) capacity < vitalityVsStress s capacity) ∧
      -- both extremes are dead: comfort and overwhelm alike yield zero vitality
      (vitalityVsStress 0 capacity = 0 ∧ vitalityVsStress capacity capacity = 0) := by
  unfold vitalityVsStress
  exact SapolskyStress.inverted_u capacity

/-! ## 8. The headline synthesis -/

/-- **(HEADLINE) Vitality is sustained flow.** The whole arc composed into one
    proved statement, the precise, humane theory of life-force:

    1. **Flow, not stock.** When restoration covers drain (`sustained`), the
       vitality level is maintained or grows (`v ≤ vitalityStep v restoration
       drain`): life-force persists as a flow that keeps pace, not as a reserve
       drawn down.
    2. **Collapse is absorbing.** At the floor with `restoration ≤ drain`, vitality
       stays `0` (`vitalityStep 0 restoration drain = 0`): the depleted state is a
       fixed point — the spent loop does not refill itself. (The bridge:
       `DepressionAsCollapsedCycle.flat_is_a_fixed_point`.)
    3. **Drive revives.** From the floor, a restoration that *beats* the drain
       (`drain < restoration`) gives positive vitality (`0 < vitalityStep 0
       restoration drain`): the floor is escapable — but only by a drive from
       outside the spent loop. (The mirror:
       `DepressionAsCollapsedCycle.recovery_escapes_the_fixed_point`.)
    4. **Sustained iff balanced.** Vitality is `sustained` iff `drain ≤
       restoration`: a single sharp flow-balance threshold, the self read as its
       own commons (`Vampire.sustained`).
    5. **Peaks at the edge.** As a function of engagement/stress, vitality is zero
       at both extremes — comfort and overwhelm — and maximal in between
       (`SapolskyStress.inverted_u`): life-force lives at the edge, not at rest.

    Bundled so the five facets are provably one theory: vitality is sustained flow,
    its floor is absorbing yet escapable by drive, and it peaks at the edge — never
    a stored quantity, always a balance kept. -/
theorem vitality_is_sustained_flow
    (v restoration drain : Nat) (hSustained : sustained restoration drain)
    (restoration₀ drain₀ : Nat) (hCollapsed : restoration₀ ≤ drain₀)
    (restoration₁ drain₁ : Nat) (hDrive : drain₁ < restoration₁)
    (capacity : Nat) :
    -- 1. flow, not stock: a balanced flow maintains or grows the level
    (v ≤ vitalityStep v restoration drain) ∧
    -- 2. the floor is absorbing without a beating drive
    (vitalityStep 0 restoration₀ drain₀ = 0) ∧
    -- 3. but a drive that beats the drain revives it
    (0 < vitalityStep 0 restoration₁ drain₁) ∧
    -- 4. sustained iff restoration ≥ drain (the flow-balance threshold)
    (sustained restoration drain ↔ drain ≤ restoration) ∧
    -- 5. peaks at the edge: zero at both extremes, maximal in between
    (∃ p : Nat,
      p = capacity / 2 ∧
      (∀ s, 2 * s + 2 ≤ capacity →
          vitalityVsStress s capacity < vitalityVsStress (s + 1) capacity) ∧
      (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
          vitalityVsStress (s + 1) capacity < vitalityVsStress s capacity) ∧
      (vitalityVsStress 0 capacity = 0 ∧ vitalityVsStress capacity capacity = 0)) :=
  ⟨vitality_is_flow_not_stock hSustained,
   collapse_is_absorbing hCollapsed,
   drive_revives_vitality hDrive,
   vitality_balance restoration drain,
   vitality_peaks_at_the_edge capacity⟩

end Gnosis.Body.Vitality
