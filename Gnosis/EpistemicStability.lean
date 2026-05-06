import Init
import Gnosis.AkerlofLemons

namespace Gnosis
namespace EpistemicStability

/-!
# Epistemic stability bifurcation

This module separates two modes:

- **Ignorance-stable**: lemons survive while peaches exit (no-signal pooling).
- **High-quality**: certified signal restores peach participation and lifts
  high-quality market weight.
-/

/-- Stable degraded mode under no signal:
lemons trade while peaches fail participation. -/
def StableRegime (vals : AkerlofLemons.SellerValues) (lemons peaches : Nat) : Prop :=
  (¬ AkerlofLemons.ValidTradeNoSignal vals lemons peaches AkerlofLemons.Good.Peach) ∧
  AkerlofLemons.ValidTradeNoSignal vals lemons peaches AkerlofLemons.Good.Lemon

/-- High-quality mode under a certified separating signal. -/
def HighQualityRegime
    (vals : AkerlofLemons.SellerValues)
    (peachPrice lemonPrice : Nat) : Prop :=
  AkerlofLemons.CertifiedSignal vals peachPrice lemonPrice ∧
  AkerlofLemons.ValidTrade vals peachPrice AkerlofLemons.Good.Peach

/-- Ignorance regime implies stable degraded mode. -/
theorem ignorance_implies_stable_regime
    (vals : AkerlofLemons.SellerValues) (lemons peaches : Nat)
    (hIgn : AkerlofLemons.IgnoranceRegime vals lemons peaches) :
    StableRegime vals lemons peaches := by
  exact AkerlofLemons.ignorance_selective_survival vals lemons peaches hIgn

/-- Certified signal implies high-quality mode. -/
theorem certified_signal_implies_high_quality
    (vals : AkerlofLemons.SellerValues) (peachPrice lemonPrice : Nat)
    (hSig : AkerlofLemons.CertifiedSignal vals peachPrice lemonPrice) :
    HighQualityRegime vals peachPrice lemonPrice := by
  refine ⟨hSig, ?_⟩
  exact AkerlofLemons.certified_signal_restores_peach_participation vals peachPrice lemonPrice hSig

/-- Bifurcation in market mass:
stable ignorance mode sits at floor while signal mode reaches ceiling. -/
theorem bifurcation_weight_floor_vs_ceiling
    (R : Nat) :
    AkerlofLemons.peachMarketWeight R false = 1 ∧
    AkerlofLemons.peachMarketWeight R true = R + 1 := by
  exact ⟨AkerlofLemons.peach_exit_forces_floor R,
    AkerlofLemons.certified_signal_recovers_ceiling R⟩

/-- Strict separation of modes when budget is positive. -/
theorem bifurcation_weight_strict_of_pos
    (R : Nat) (hR : 0 < R) :
    AkerlofLemons.peachMarketWeight R true >
    AkerlofLemons.peachMarketWeight R false := by
  exact AkerlofLemons.certified_signal_weight_gt_floor_of_pos R hR

/-- Existing witness market instantiates stable degraded regime. -/
theorem witness_market_stable_regime :
    StableRegime AkerlofLemons.witnessVals 4 1 := by
  exact ignorance_implies_stable_regime
    AkerlofLemons.witnessVals 4 1
    AkerlofLemons.witness_is_ignorance_regime

end EpistemicStability
end Gnosis
