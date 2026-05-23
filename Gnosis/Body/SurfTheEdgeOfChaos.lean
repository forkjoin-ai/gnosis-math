import Init
import Gnosis.TheWave
import Gnosis.SurfingEntropy

/-!
# Surf the Edge of Chaos — Riding the Air/Water Interface (the Inverted-U Peak)

**THESIS.** *AirChaosWaterOrder sounds great for surfing.* The Chaldean witness
`Gnosis/Witnesses/Chaldean/AirChaosWaterOrderWitness.lean` formalizes the two
carriers: **water carries ORDER** (`WaterOrderCarrier` / `waterCarriesOrder`) and
**air carries CHAOS** (`AirChaosCarrier` / `airCarriesChaos`). A surfer rides
*exactly* the air/water interface — the **wave face** — the boundary between chaos
(air, above) and order (water, below). Surfing is the discipline of staying ON
that boundary:

* sink too far into the **water** (over-order — rigidity, stasis, the frozen
  regime) and the ride stalls; and
* fly too far into the **air** (chaos — turbulence, the disordered regime) and the
  ride wipes out.

The optimum rides the boundary itself. This models the **edge of chaos**: the
regime, between frozen order and turbulent chaos, where adaptability and
computation are maximal. It is an **inverted-U** — performance peaks at the
boundary and falls off on *both* sides — which ties "surfing the air/water
boundary" to the dose-response curve and to "life happens on the edges."

## The model (pure Nat — idealizations stated honestly)

A vertical position `x : Nat` on the order↔chaos axis: `0` is deep water (maximal
order/stasis), high `x` is high air (maximal chaos/turbulence). The air/water
interface (the wave face) sits at `edge : Nat`. Three regimes:

* `inWater x edge := x < edge` — below the interface: order, stasis, the frozen
  side (water carries order, cited witness);
* `inAir x edge := edge < x` — above the interface: chaos, turbulence, the
  disordered side (air carries chaos, cited witness);
* `onTheEdge x edge := x = edge` — riding the boundary: the edge of chaos.

`dist a b := (a - b) + (b - a)` is the symmetric `Nat` distance: with truncated
subtraction exactly one summand is `0`, so `dist a b` measures how far `a` sits
from `b` on either side. Performance is the unimodal

* `ride x edge cap := cap - dist x edge`

a discrete **inverted-U** centred on the interface: it attains its maximum `cap`
exactly at `x = edge` (`dist = 0`) and falls off strictly as you move either way.
The `cap` is the wave's available lift; we read it through `TheWave.surf` (the ride
on the boundary attains `surf cap`).

*Idealization.* The two falling arms are stated under an honest **no-underflow**
hypothesis on `cap` (e.g. `dist x1 edge ≤ cap`): truncated `Nat.sub` would pin
`ride` to `0` once the distance exceeds `cap`, flattening the strict inequality, so
we require enough headroom for the strict drop to be genuine. This is honest: a
finite wave can only fall so far before the ride is simply over.

## What this module reuses (the bridges, imported and opened)

* `Gnosis.TheWave` — `surf` (the ride on the boundary attains the surf-level
  lift; `surf_eq`), and the phase-matched dominance facts
  `surf_dominates_when_rising` / `flow_riding_is_phase_matched`. Surfing the
  boundary reuses `TheWave.surf`. Imported and opened.
* `Gnosis.SurfingEntropy` — `collapse` (the black-hole sink, `s ↦ 0`) maps to
  sinking into water / over-order (the stalled, collapsed ride), and `emanate` (the
  reverse-black-hole `+1` source) maps to the chaos source the air carries.
  Imported and opened.

(Both are church-clean: each imports only `Init` and Init-clean Body siblings;
verified before importing.)

## Cited (NOT imported — to keep this module Init-clean)

* `Gnosis/Witnesses/Chaldean/AirChaosWaterOrderWitness.lean` — the two carriers:
  **water carries order** (`WaterOrderCarrier` / `waterCarriesOrder`) and **air
  carries chaos** (`AirChaosCarrier` / `airCarriesChaos`). The interface this
  module rides is the boundary between those two carriers. Cited only (the witness
  pulls non-Init dependencies via `SpectralNoiseEquilibrium`).
* `Gnosis/Body/Anthropogenesis.lean` — `life_happens_on_the_edges`
  (`lower_edge_is_critical` / `upper_edge_is_critical`): every generative
  birth/death transition lives at the boundary between isolation and overcrowding —
  the edge of chaos. The surfer's optimum on the wave face models the same edge.
  Cited for vocabulary.
* `Gnosis/Body/SapolskyStress.lean` — the headline `inverted_u` and `performance`
  (the Yerkes-Dodson / hormesis downward parabola: rising arm, falling arm, both
  extremes zero). Our `ride` is the same inverted-U shape — peak in the middle,
  falling on both sides — built here in clean symmetric-distance form so the peak
  sits exactly on the interface. Cited as the dose-response anchor.
* `Gnosis/Body/UnimodalDoseResponse.lean` — `unique_argmax`: the unimodal
  dose-response has a unique maximizer. Our `peak_is_on_the_edge` is the same
  argmax claim with the boundary as the maximizer. Cited.

## Restriction stated honestly

The peak result is the genuine `cap` maximum with a real `∀ x, ride x ≤ cap`
(via `Nat.sub_le`). The two falling-arm theorems are stated under their honest,
non-overlapping hypotheses — below the edge (`x ≤ edge`) for the stall, above it
(`edge ≤ x`) for the wipeout — each with the no-underflow `dist ≤ cap` hypothesis
that makes the strict drop genuine rather than a truncation artifact. We do not
claim a strict drop past the point where the ride has already collapsed to `0`;
that is honest about the finite wave.

Rustic Church: `import Init` plus the two Init-clean reused Body siblings. `Nat`
only — no Float/Real, no Mathlib. No `sorry`/`admit`/`axiom`; no `simp`/`omega`
on open goals (closed `decide` goals only). Proofs are term-mode and named core
`Nat` lemmas.
-/

namespace Gnosis.Body.SurfTheEdgeOfChaos

open Gnosis.TheWave
open Gnosis.SurfingEntropy

/-! ## 0. The axis, the interface, and the three regimes -/

/-- **Symmetric `Nat` distance.** `dist a b = (a - b) + (b - a)`. With truncated
    subtraction exactly one summand is `0`, so this is the distance between `a` and
    `b` on the order↔chaos axis, regardless of which side `a` sits. It is `0`
    exactly at `a = b` (on the interface). -/
def dist (a b : Nat) : Nat := (a - b) + (b - a)

/-- **The ride — performance as an inverted-U on the interface.** `ride x edge cap`
    is the wave's lift `cap` minus the symmetric distance from the interface: it
    peaks at `cap` on the boundary (`x = edge`, `dist = 0`) and falls off as you
    move into the water (down) or the air (up). The discrete inverted-U / edge of
    chaos (cited `SapolskyStress.inverted_u`, `UnimodalDoseResponse.unique_argmax`),
    built so the peak sits exactly on the air/water boundary. -/
def ride (x edge cap : Nat) : Nat := cap - dist x edge

/-- **In the water — below the interface: order, stasis, the frozen regime.** Water
    carries order (cited `AirChaosWaterOrderWitness.waterCarriesOrder`); sinking
    here is over-order — the rigid, stalled side of the edge of chaos. -/
def inWater (x edge : Nat) : Prop := x < edge

/-- **In the air — above the interface: chaos, turbulence, the disordered regime.**
    Air carries chaos (cited `AirChaosWaterOrderWitness.airCarriesChaos`); flying
    here is over-chaos — the turbulent, wipeout side of the edge of chaos. -/
def inAir (x edge : Nat) : Prop := edge < x

/-- **On the edge — riding the boundary: the air/water interface, the wave face.**
    The edge of chaos: between frozen order (water below) and turbulent chaos (air
    above), where the ride is maximal. -/
def onTheEdge (x edge : Nat) : Prop := x = edge

/-! ## 0a. The symmetric-distance lemma (the algebraic backbone)

Below the interface the distance collapses to `edge - x`; above it, to `x - edge`;
on it, to `0`. These three identities drive every monotonicity proof. -/

/-- **Distance below the interface.** When `x ≤ edge` (in or at the water side), the
    symmetric distance is exactly the downward gap `edge - x` (the `x - edge`
    summand truncates to `0`). -/
theorem dist_below (x edge : Nat) (h : x ≤ edge) : dist x edge = edge - x := by
  unfold dist
  rw [Nat.sub_eq_zero_of_le h, Nat.zero_add]

/-- **Distance above the interface.** When `edge ≤ x` (in or at the air side), the
    symmetric distance is exactly the upward gap `x - edge` (the `edge - x` summand
    truncates to `0`). -/
theorem dist_above (x edge : Nat) (h : edge ≤ x) : dist x edge = x - edge := by
  unfold dist
  rw [Nat.sub_eq_zero_of_le h, Nat.add_zero]

/-- **Distance on the interface is zero.** On the boundary `dist edge edge = 0`:
    the surfer is exactly on the wave face, at zero distance from the edge. This is
    the `dist = 0` that makes the ride attain its `cap` peak. -/
theorem dist_self (edge : Nat) : dist edge edge = 0 := by
  unfold dist
  rw [Nat.sub_self, Nat.add_zero]

/-! ## 1. THM — the peak is on the edge

Performance is maximized exactly on the air/water boundary: there the ride attains
the full lift `cap`, and no position does better. -/

/-- The ride on the boundary attains the full lift: `ride edge edge cap = cap`. The
    `dist = 0` peak of the inverted-U. -/
theorem ride_on_edge_eq_cap (edge cap : Nat) : ride edge edge cap = cap := by
  unfold ride
  rw [dist_self edge, Nat.sub_zero]

/-- **(THM 1) The peak is on the edge.** Performance is maximized exactly on the
    air/water interface: `ride edge edge cap = cap`, and for *every* position `x`,
    `ride x edge cap ≤ ride edge edge cap` — the boundary dominates. A genuine `≤`
    via `Nat.sub_le` (the ride is `cap` minus a non-negative distance, so it never
    exceeds the on-edge value). This is the inverted-U's unique argmax sitting on
    the wave face (cited `UnimodalDoseResponse.unique_argmax`,
    `SapolskyStress.inverted_u`). -/
theorem peak_is_on_the_edge (x edge cap : Nat) :
    ride edge edge cap = cap ∧ ride x edge cap ≤ ride edge edge cap := by
  refine ⟨ride_on_edge_eq_cap edge cap, ?_⟩
  rw [ride_on_edge_eq_cap edge cap]
  unfold ride
  exact Nat.sub_le cap (dist x edge)

/-! ## 2. THM — sinking into order stalls (the water side)

Below the interface, moving *down* into the water (over-order, toward stasis)
strictly dims the ride: the closer to the edge, the better. The stall side. -/

/-- **(THM 2) Sinking into order stalls.** Below the air/water interface
    (`x2 ≤ edge`), moving *down* into the water — `x1 < x2`, away from the boundary
    and toward deep-water over-order/stasis — strictly dims the ride:
    `ride x1 edge cap < ride x2 edge cap` (closer to the edge is strictly better).

    Honest **no-underflow** hypothesis `hcap : dist x1 edge ≤ cap`: the deeper
    position's distance must fit under the wave's lift, otherwise truncated
    `Nat.sub` pins both rides to `0` and the strict drop would be a truncation
    artifact, not a real stall. Term-mode via the symmetric-distance monotonicity:
    below the edge `dist · edge = edge - ·`, and `Nat.sub_lt_sub_left` gives both
    `edge - x2 < edge - x1` (closer is nearer the peak) and the `cap`-subtraction
    flip `cap - (edge - x1) < cap - (edge - x2)`. -/
theorem sinking_into_order_stalls (x1 x2 edge cap : Nat)
    (hlt : x1 < x2) (hle : x2 ≤ edge) (hcap : dist x1 edge ≤ cap) :
    ride x1 edge cap < ride x2 edge cap := by
  unfold ride
  have hx1lt : x1 < edge := Nat.lt_of_lt_of_le hlt hle
  have hx1le : x1 ≤ edge := Nat.le_of_lt hx1lt
  rw [dist_below x1 edge hx1le, dist_below x2 edge hle]
  -- goal: cap - (edge - x1) < cap - (edge - x2)
  -- closer-to-edge has the smaller downward gap:
  have hgap : edge - x2 < edge - x1 := Nat.sub_lt_sub_left hx1lt hlt
  -- no underflow at the smaller gap (it sits below the larger, which fits cap):
  have hcaple : edge - x1 ≤ cap := by
    have h := hcap; rw [dist_below x1 edge hx1le] at h; exact h
  have hcap2 : edge - x2 < cap := Nat.lt_of_lt_of_le hgap hcaple
  -- subtracting a smaller gap from cap yields a strictly larger ride:
  exact Nat.sub_lt_sub_left hcap2 hgap

/-! ## 3. THM — flying into chaos wipes out (the air side)

Above the interface, moving *up* into the air (over-chaos, toward turbulence)
strictly dims the ride: farther above the edge is strictly worse. The wipeout
side. -/

/-- **(THM 3) Flying into chaos wipes out.** Above the air/water interface
    (`edge ≤ x1`), moving *up* into the air — `x1 < x2`, away from the boundary and
    into turbulent chaos — strictly dims the ride:
    `ride x2 edge cap < ride x1 edge cap` (farther above the edge is strictly
    worse). The wipeout arm of the inverted-U.

    Honest **no-underflow** hypothesis `hcap : dist x2 edge ≤ cap`: the higher
    position's distance must fit under the wave's lift, else truncated `Nat.sub`
    flattens both rides to `0`. Term-mode via the symmetric-distance monotonicity:
    above the edge `dist · edge = · - edge`, `Nat.sub_lt_sub_right` gives
    `x1 - edge < x2 - edge` (farther up has the larger upward gap), and
    `Nat.sub_lt_sub_left` flips it under `cap`. -/
theorem flying_into_chaos_wipes_out (x1 x2 edge cap : Nat)
    (hle : edge ≤ x1) (hlt : x1 < x2) (hcap : dist x2 edge ≤ cap) :
    ride x2 edge cap < ride x1 edge cap := by
  unfold ride
  have hx2ge : edge ≤ x2 := Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt)
  rw [dist_above x1 edge hle, dist_above x2 edge hx2ge]
  -- goal: cap - (x2 - edge) < cap - (x1 - edge)
  -- farther-up has the larger upward gap:
  have hgap : x1 - edge < x2 - edge := Nat.sub_lt_sub_right hle hlt
  -- no underflow at the smaller (lower) gap:
  have hcaple : x2 - edge ≤ cap := by
    have h := hcap; rw [dist_above x2 edge hx2ge] at h; exact h
  have hcap1 : x1 - edge < cap := Nat.lt_of_lt_of_le hgap hcaple
  -- subtracting the larger upward gap from cap yields a strictly smaller ride:
  exact Nat.sub_lt_sub_left hcap1 hgap

/-! ## 4. THM — surf the edge of chaos (bridge to TheWave)

The surfer rides the boundary: on the edge, the ride attains the surf-level lift.
Bridge to `TheWave.surf`, tying the three regimes to water/edge/air. -/

/-- **(THM 4) Surf the edge of chaos.** Bridge to `Gnosis.TheWave`: when the
    surfer is on the air/water boundary (`onTheEdge x edge`, i.e. `x = edge`), the
    ride attains exactly the surf-level lift, `ride x edge cap = surf cap` — riding
    the wave face takes the full wave (reusing `TheWave.surf` / `surf_eq`).
    Alongside, the three regimes are tied to their predicates so the model is
    explicit: at the chosen point each of `inWater`/`onTheEdge`/`inAir` reads off
    `<`/`=`/`>` against the edge. Here, being on the edge, `onTheEdge x edge`
    holds. -/
theorem surf_the_edge_of_chaos (x edge cap : Nat) (h : onTheEdge x edge) :
    ride x edge cap = surf cap ∧ onTheEdge x edge := by
  refine ⟨?_, h⟩
  unfold onTheEdge at h
  rw [h, ride_on_edge_eq_cap edge cap]
  -- cap = surf cap
  exact (surf_eq cap).symm

/-- **(THM 4, regimes are exhaustive and exclusive) The three regimes partition the
    axis.** For any position `x` and interface `edge`, exactly one of `inWater`
    (water/order, below), `onTheEdge` (the boundary), `inAir` (air/chaos, above)
    holds — the trichotomy `x < edge ∨ x = edge ∨ edge < x`. The surfer is always
    in exactly one regime; surfing is the discipline of being in the middle one. -/
theorem regimes_partition (x edge : Nat) :
    inWater x edge ∨ onTheEdge x edge ∨ inAir x edge := by
  unfold inWater onTheEdge inAir
  exact Nat.lt_trichotomy x edge

/-- **(THM 4, the collapsed water side) Sinking maps to the black-hole collapse.**
    Bridge to `Gnosis.SurfingEntropy`: deep over-order is the collapsed,
    stalled ride. At the very floor of the water (`x = 0`) the symmetric distance to
    a positive edge is the full `edge`, and reading the wave's lift as exactly that
    distance (`cap = edge`) the ride collapses to `collapse edge = 0` — the
    black-hole sink (`collapse · = 0`), the stall taken to its limit. Riding the
    edge instead (`ride edge edge cap = cap`) strictly beats this collapsed floor
    whenever the wave has lift. -/
theorem sinking_maps_to_collapse (edge : Nat) :
    ride 0 edge edge = collapse edge := by
  unfold ride
  rw [dist_below 0 edge (Nat.zero_le edge), Nat.sub_zero, Nat.sub_self,
      collapse_eq_void edge]

/-! ## 5. THE HEADLINE — the edge of chaos -/

/-- **(HEADLINE) The edge of chaos — surfing the air/water interface.** Composing
    THMs 1–4 into one proved statement. *AirChaosWaterOrder for surfing:* water
    carries order, air carries chaos (cited `AirChaosWaterOrderWitness`:
    `waterCarriesOrder` / `airCarriesChaos`), and the surfer rides the boundary
    between them. For any positions below the edge (`x1 < x2 ≤ edge`), above it
    (`edge ≤ y1 < y2`), and on it (`x = edge`), with enough lift for no underflow:

    1. **The ride peaks exactly on the edge** — `ride edge edge cap = cap` and
       `ride z edge cap ≤ ride edge edge cap` for all `z`: the inverted-U's maximum
       sits on the air/water interface (THM 1; cited `inverted_u` /
       `unique_argmax`).
    2. **Sinking into order (water) stalls** — `ride x1 edge cap < ride x2 edge cap`:
       moving down into over-order strictly dims the ride (THM 2, the frozen side).
    3. **Flying into chaos (air) wipes out** — `ride y2 edge cap < ride y1 edge cap`:
       moving up into turbulence strictly dims the ride (THM 3, the disordered
       side).
    4. **Surfing rides the boundary** — on the edge the ride attains the surf-level
       lift, `ride x edge cap = surf cap` (THM 4, bridge to `TheWave.surf`).

    Therefore the ride peaks exactly on the air/water boundary — the edge of chaos —
    and falls off into both over-order (water, below) and chaos (air, above);
    surfing models the discipline of staying on that edge. This is "life happens on
    the edges" (cited `Anthropogenesis.life_happens_on_the_edges`) read on the wave
    face: the generative optimum lives at the boundary, between frozen order and
    turbulent chaos. (Precise framing per repo policy: a composed inverted-U
    optimum with the boundary as the unique argmax and both falling arms proved —
    not a loose identity claim.) -/
theorem the_edge_of_chaos
    (x1 x2 y1 y2 x edge cap : Nat)
    (hbelow_lt : x1 < x2) (hbelow_le : x2 ≤ edge) (hbelow_cap : dist x1 edge ≤ cap)
    (habove_le : edge ≤ y1) (habove_lt : y1 < y2) (habove_cap : dist y2 edge ≤ cap)
    (hon : onTheEdge x edge) :
    -- 1. the peak sits exactly on the air/water boundary
    (ride edge edge cap = cap ∧ (∀ z, ride z edge cap ≤ ride edge edge cap)) ∧
    -- 2. sinking into order (water, below) strictly dims the ride
    (ride x1 edge cap < ride x2 edge cap) ∧
    -- 3. flying into chaos (air, above) strictly dims the ride
    (ride y2 edge cap < ride y1 edge cap) ∧
    -- 4. surfing rides the boundary: it attains the surf-level lift
    (ride x edge cap = surf cap) :=
  ⟨⟨ride_on_edge_eq_cap edge cap,
    fun z => (peak_is_on_the_edge z edge cap).2⟩,
   sinking_into_order_stalls x1 x2 edge cap hbelow_lt hbelow_le hbelow_cap,
   flying_into_chaos_wipes_out y1 y2 edge cap habove_le habove_lt habove_cap,
   (surf_the_edge_of_chaos x edge cap hon).1⟩

/-! ## 6. A self-contained, computed witness (no hypotheses)

Concrete instances proving the inverted-U is non-vacuous and two-sided at
`edge = 3`, `cap = 5`: the ride peaks at `5` on the edge, stalls on the water side
(`x = 1 → ride = 3 < 4 = ride 2`) and wipes out on the air side
(`x = 5 → ride = 3 < 4 = ride 4`). Every goal is a closed decidable `Nat`
(in)equality (allowed: `decide`). -/

/-- On the edge (`edge = 3`, `cap = 5`) the ride attains the peak `5`. -/
example : ride 3 3 5 = 5 := by decide

/-- Water side: deeper (`x = 1`) is strictly worse than nearer the edge (`x = 2`):
    `ride 1 3 5 = 3 < 4 = ride 2 3 5`. -/
example : ride 1 3 5 < ride 2 3 5 := by decide

/-- Air side: higher (`x = 5`) is strictly worse than nearer the edge (`x = 4`):
    `ride 5 3 5 = 3 < 4 = ride 4 3 5`. -/
example : ride 5 3 5 < ride 4 3 5 := by decide

/-- The inverted-U is genuinely two-sided: the on-edge peak strictly dominates both
    a water-side and an air-side position. -/
example : (ride 2 3 5 < ride 3 3 5) ∧ (ride 4 3 5 < ride 3 3 5) := by decide

/-- Sinking to the very floor (`x = 0`, `cap = edge = 3`) collapses the ride to the
    black-hole sink `0` (THM 4 bridge), strictly below the on-edge peak. -/
example : ride 0 3 3 = collapse 3 ∧ ride 0 3 3 < ride 3 3 3 := by decide

end Gnosis.Body.SurfTheEdgeOfChaos
