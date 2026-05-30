import Gnosis.HotellingMeshSprawl
import Gnosis.HospitalityTransportCommerce

/-!
# HospitalityThreeSistersCollective — when collectives form (cooperation vs competition)

`HotellingMeshSprawl` gives the COMPETITION pole (same-category rivals repel → spread).
Three Sisters companion-planting gives the COOPERATION pole (mutualist companions
attract → cluster). A COLLECTIVE forms exactly where cooperation beats competition,
and that raises the plot's COMMERCE — hence its HOSPITALITY
(`Gnosis/HospitalityTransportCommerce`). Two cases fall out:
  • INTRA-industry — a guild / district: same-category businesses cooperate (shared
    destination) hard enough to OVERRIDE their market-split rivalry.
  • INTER-industry — the classic Three Sisters: complementary categories (no rivalry)
    cluster on any positive mutual synergy, each lifting the others' catchment.

Init-only; named `Nat` lemmas only (NO omega, per RUSTIC_CHURCH.md); propext-at-most.
-/

namespace Gnosis
namespace HospitalityThreeSistersCollective

open Gnosis.HospitalityTransportCommerce (hospitality)

/-- Three Sisters cooperation modes (mirrors aeon-3d `PhyleCooperationMode`). -/
inductive CoopMode where
  | mutualism      -- both companions benefit (corn ⊕ beans ⊕ squash)
  | commensalism   -- one benefits, the other is unaffected
  | neutral        -- no interaction
  | competition    -- both lose (same niche) — contributes rivalry, not synergy
  deriving DecidableEq, Repr

/-- Cooperation synergy a companion contributes in a given mode. -/
def modeSynergy : CoopMode → Nat
  | .mutualism    => 2
  | .commensalism => 1
  | .neutral      => 0
  | .competition  => 0

/-- A business's commerce STANDING ALONE: just its own catchment. -/
def solo (catchment : Nat) : Nat := catchment

/-- A business's commerce CO-LOCATED in a collective: its catchment plus companion
    cooperation `synergy`, minus same-niche `rivalry` (Nat-truncated — rivalry can
    erase synergy but never go below zero). -/
def inCollective (catchment synergy rivalry : Nat) : Nat :=
  (catchment + synergy) - rivalry

/-- A collective is worth forming iff cooperation strictly beats competition.
    `@[reducible]` so `decide` sees the underlying `<` in the witnesses. -/
@[reducible] def collectiveForms (synergy rivalry : Nat) : Prop := rivalry < synergy

/-- CORE: when a collective forms (synergy > rivalry), co-locating strictly raises a
    business's commerce above standing alone. -/
theorem collective_raises_commerce
    (catchment synergy rivalry : Nat) (h : rivalry < synergy) :
    solo catchment < inCollective catchment synergy rivalry := by
  unfold solo inCollective
  rw [Nat.add_sub_assoc (Nat.le_of_lt h)]
  exact Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt h)

/-- …and that lifts straight into HOSPITALITY (cooperation made hospitable). -/
theorem collective_raises_hospitality
    (base transport catchment synergy rivalry : Nat) (h : rivalry < synergy) :
    hospitality base transport (solo catchment)
      < hospitality base transport (inCollective catchment synergy rivalry) := by
  unfold hospitality
  exact Nat.add_lt_add_left
    (collective_raises_commerce catchment synergy rivalry h) (base + transport)

/-- PURE COMPETITION (no cooperation): no collective forms — businesses disperse,
    recovering the bare Hotelling spread (`HotellingMeshSprawl`). -/
theorem no_cooperation_no_collective (rivalry : Nat) :
    ¬ collectiveForms 0 rivalry := by
  unfold collectiveForms
  exact Nat.not_lt_zero rivalry

/-- INTRA-INDUSTRY GUILD: `n` same-category businesses in `mutualism` form a
    collective once their shared-destination synergy beats their rivalry — Hotelling
    repulsion OVERRIDDEN by cooperation. -/
theorem intra_industry_guild_forms
    (catchment rivalry n : Nat) (h : rivalry < n * modeSynergy CoopMode.mutualism) :
    solo catchment < inCollective catchment (n * modeSynergy CoopMode.mutualism) rivalry :=
  collective_raises_commerce catchment (n * modeSynergy CoopMode.mutualism) rivalry h

/-- INTER-INDUSTRY (Three Sisters): complementary categories have NO rivalry, so any
    positive mutual synergy forms a collective — each lifts the others' catchment. -/
theorem inter_industry_collective_forms
    (catchment synergy : Nat) (h : 0 < synergy) :
    solo catchment < inCollective catchment synergy 0 :=
  collective_raises_commerce catchment synergy 0 h

-- ── Witnesses (decide) ────────────────────────────────────────────────────────

/-- A 3-shop guild (mutualism, synergy 6) overrides rivalry 4 — a district forms. -/
theorem guild_of_three_forms :
    collectiveForms (3 * modeSynergy CoopMode.mutualism) 4 := by decide

/-- Café ⊕ bookstore (different industries, rivalry 0, mutualism) — Three Sisters. -/
theorem cafe_bookstore_collective :
    collectiveForms (modeSynergy CoopMode.mutualism) 0 := by decide

/-- Two rivals with NO cooperation (synergy 0, rivalry 3) do NOT collect — spread. -/
theorem rivals_disperse : ¬ collectiveForms 0 3 := by decide

-- Axiom audit (target: propext-at-most, no omega / native_decide):
#print axioms collective_raises_commerce
#print axioms collective_raises_hospitality
#print axioms intra_industry_guild_forms
#print axioms inter_industry_collective_forms

end HospitalityThreeSistersCollective
end Gnosis
