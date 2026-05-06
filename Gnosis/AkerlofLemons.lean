import Init
import Gnosis.GodFormula

namespace Gnosis
namespace AkerlofLemons

open Gnosis (godWeight godWeight_floor)

/-!
# Akerlof "Lemons" model (information asymmetry collapse)

This module formalizes a two-quality used-goods market:

- sellers know actual quality (`Lemon` vs `Peach`),
- buyers observe only pooled distribution (no signal),
- trade is valid only when offered price meets seller reservation value.

The collapse theorem shows: when pooled no-signal price is low enough,
high-quality (`Peach`) participation fails, and the high-quality market
weight collapses to the clinamen floor.
-/

/-- Quality states. -/
inductive Good where
  | Lemon
  | Peach
  deriving DecidableEq, Repr

/-- Seller reservation values by actual quality. -/
structure SellerValues where
  lemonValue : Nat
  peachValue : Nat
  peach_gt_lemon : lemonValue < peachValue

/-- Seller knows actual quality, so reservation is quality-conditional. -/
def sellerValue (vals : SellerValues) : Good → Nat
  | .Lemon => vals.lemonValue
  | .Peach => vals.peachValue

/-- Buyers with no signal offer one pooled price from expected quality:
weighted average with Nat floor division. -/
def pooledBuyerPrice (vals : SellerValues) (lemons peaches : Nat) : Nat :=
  let total := lemons + peaches
  if total = 0 then
    0
  else
    (lemons * vals.lemonValue + peaches * vals.peachValue) / total

/-- Participation/trade validity: offered buyer price meets seller reservation. -/
def ValidTrade (vals : SellerValues) (buyerPrice : Nat) (g : Good) : Prop :=
  sellerValue vals g ≤ buyerPrice

/-- In a no-signal market, both qualities face the same pooled bid. -/
def ValidTradeNoSignal (vals : SellerValues) (lemons peaches : Nat) (g : Good) : Prop :=
  ValidTrade vals (pooledBuyerPrice vals lemons peaches) g

instance decValidTrade (vals : SellerValues) (buyerPrice : Nat) (g : Good) :
    Decidable (ValidTrade vals buyerPrice g) := by
  unfold ValidTrade
  infer_instance

instance decValidTradeNoSignal (vals : SellerValues) (lemons peaches : Nat) (g : Good) :
    Decidable (ValidTradeNoSignal vals lemons peaches g) := by
  unfold ValidTradeNoSignal
  infer_instance

/-- "High enough lemons" represented as price depression below peach reservation. -/
def LemonDominated (vals : SellerValues) (lemons peaches : Nat) : Prop :=
  pooledBuyerPrice vals lemons peaches < vals.peachValue

/-- If pooled no-signal bid is below peach reservation, peach exits. -/
theorem peach_exits_when_price_below (vals : SellerValues) (price : Nat)
    (h : price < vals.peachValue) :
    ¬ ValidTrade vals price Good.Peach := by
  unfold ValidTrade sellerValue
  intro htrade
  exact Nat.not_lt_of_ge htrade h

/-- Lemon-dominated no-signal market implies peach non-participation. -/
theorem lemon_dominated_implies_peach_exit (vals : SellerValues) (lemons peaches : Nat)
    (hDom : LemonDominated vals lemons peaches) :
    ¬ ValidTradeNoSignal vals lemons peaches Good.Peach := by
  unfold LemonDominated ValidTradeNoSignal at *
  exact peach_exits_when_price_below vals (pooledBuyerPrice vals lemons peaches) hDom

/-- High-quality market active flag under no-signal pooled price. -/
def peachMarketActive (vals : SellerValues) (lemons peaches : Nat) : Bool :=
  if ValidTradeNoSignal vals lemons peaches Good.Peach then true else false

/-- High-quality market weight:
active -> ceiling side (`v = 0`), exited -> floor side (`v = R`). -/
def peachMarketWeight (R : Nat) (active : Bool) : Nat :=
  if active then godWeight R 0 else godWeight R R

/-- If peaches exit, high-quality market weight hits the floor. -/
theorem peach_exit_forces_floor (R : Nat) :
    peachMarketWeight R false = 1 := by
  unfold peachMarketWeight
  simp [godWeight_floor]

/-- Main collapse theorem:
under lemon-dominated no-signal pricing, peach market collapses to floor. -/
theorem lemon_market_collapse_to_floor
    (vals : SellerValues) (R lemons peaches : Nat)
    (hDom : LemonDominated vals lemons peaches) :
    peachMarketWeight R (peachMarketActive vals lemons peaches) = 1 := by
  unfold peachMarketActive
  by_cases hActive : ValidTradeNoSignal vals lemons peaches Good.Peach
  · -- contradiction with lemon-dominated participation failure
    exfalso
    exact lemon_dominated_implies_peach_exit vals lemons peaches hDom hActive
  · simp [hActive, peach_exit_forces_floor]

/-- Executable witness: one concrete lemons-heavy pool. -/
def witnessVals : SellerValues :=
  { lemonValue := 2
    peachValue := 5
    peach_gt_lemon := by decide }

theorem witness_pool_is_lemon_dominated :
    LemonDominated witnessVals 4 1 := by
  unfold LemonDominated pooledBuyerPrice witnessVals
  decide

theorem witness_collapse :
    peachMarketWeight 10 (peachMarketActive witnessVals 4 1) = 1 := by
  exact lemon_market_collapse_to_floor witnessVals 10 4 1 witness_pool_is_lemon_dominated

/-! ## Ignorance regime (epistemic asymmetry as structural vent) -/

/-- Ignorance regime: no-signal pooled pricing depresses valuation below peach
reservation while still supporting lemon participation. This captures adverse
selection without full market shutdown. -/
def IgnoranceRegime (vals : SellerValues) (lemons peaches : Nat) : Prop :=
  LemonDominated vals lemons peaches ∧
  vals.lemonValue ≤ pooledBuyerPrice vals lemons peaches

/-- In the ignorance regime, high-quality participation is impossible. -/
theorem ignorance_forces_peach_exit
    (vals : SellerValues) (lemons peaches : Nat)
    (hIgn : IgnoranceRegime vals lemons peaches) :
    ¬ ValidTradeNoSignal vals lemons peaches Good.Peach := by
  exact lemon_dominated_implies_peach_exit vals lemons peaches hIgn.1

/-- In the same regime, low-quality goods can still participate. -/
theorem ignorance_keeps_lemon_trade
    (vals : SellerValues) (lemons peaches : Nat)
    (hIgn : IgnoranceRegime vals lemons peaches) :
    ValidTradeNoSignal vals lemons peaches Good.Lemon := by
  unfold ValidTradeNoSignal ValidTrade sellerValue
  exact hIgn.2

/-- Selective survival theorem: ignorance produces a lemons-only traded market. -/
theorem ignorance_selective_survival
    (vals : SellerValues) (lemons peaches : Nat)
    (hIgn : IgnoranceRegime vals lemons peaches) :
    (¬ ValidTradeNoSignal vals lemons peaches Good.Peach) ∧
    ValidTradeNoSignal vals lemons peaches Good.Lemon := by
  exact ⟨ignorance_forces_peach_exit vals lemons peaches hIgn,
    ignorance_keeps_lemon_trade vals lemons peaches hIgn⟩

/-- A weak common-knowledge participation postulate for high-quality goods:
if quality were effectively common-knowledge at the market level, peach should
remain tradable at the prevailing market bid. -/
def CommonKnowledgePeachParticipation
    (vals : SellerValues) (lemons peaches : Nat) : Prop :=
  ValidTradeNoSignal vals lemons peaches Good.Peach

/-- Ignorance regime is incompatible with the common-knowledge peach-participation
postulate: this is the formal skepticism witness. -/
theorem ignorance_refutes_common_knowledge_peach_participation
    (vals : SellerValues) (lemons peaches : Nat)
    (hIgn : IgnoranceRegime vals lemons peaches) :
    ¬ CommonKnowledgePeachParticipation vals lemons peaches := by
  unfold CommonKnowledgePeachParticipation
  exact ignorance_forces_peach_exit vals lemons peaches hIgn

/-- Witness instance: the existing witness pool is an ignorance regime. -/
theorem witness_is_ignorance_regime :
    IgnoranceRegime witnessVals 4 1 := by
  refine ⟨witness_pool_is_lemon_dominated, ?_⟩
  unfold pooledBuyerPrice witnessVals
  decide

/-! ## Signal bridge (separating signal restores high-quality participation) -/

/-- Certified separating signal: buyer can condition price on observed quality. -/
def CertifiedSignal (vals : SellerValues) (peachPrice lemonPrice : Nat) : Prop :=
  vals.peachValue ≤ peachPrice ∧ vals.lemonValue ≤ lemonPrice

instance decidableCertifiedSignal (vals : SellerValues) (ppe lpe : Nat) :
    Decidable (CertifiedSignal vals ppe lpe) := by
  unfold CertifiedSignal
  infer_instance

/-- Under a certified signal, peach trade is valid at the peach-tagged price. -/
theorem certified_signal_restores_peach_participation
    (vals : SellerValues) (peachPrice lemonPrice : Nat)
    (hSig : CertifiedSignal vals peachPrice lemonPrice) :
    ValidTrade vals peachPrice Good.Peach := by
  unfold CertifiedSignal ValidTrade sellerValue at *
  exact hSig.1

/-- Signal-active high-quality market weight uses the peach (active) branch. -/
theorem certified_signal_lifts_peach_market_weight (R : Nat) :
    peachMarketWeight R true = godWeight R 0 := by
  unfold peachMarketWeight
  simp

/-- Certified signal weakly lifts peach-market weight above floor. -/
theorem certified_signal_weight_ge_floor (R : Nat) :
    peachMarketWeight R true ≥ peachMarketWeight R false := by
  unfold peachMarketWeight
  rw [Gnosis.godWeight_ceiling, Gnosis.godWeight_floor]
  exact Nat.succ_le_succ (Nat.zero_le R)

/-- Strict lift holds for strictly positive market budget. -/
theorem certified_signal_weight_gt_floor_of_pos (R : Nat) (hR : 0 < R) :
    peachMarketWeight R true > peachMarketWeight R false := by
  unfold peachMarketWeight
  rw [Gnosis.godWeight_ceiling, Gnosis.godWeight_floor]
  exact Nat.succ_lt_succ hR

/-- Strong form: certified signal recovers ceiling weight `R + 1`. -/
theorem certified_signal_recovers_ceiling (R : Nat) :
    peachMarketWeight R true = R + 1 := by
  unfold peachMarketWeight
  simp [Gnosis.godWeight_ceiling]

end AkerlofLemons
end Gnosis
