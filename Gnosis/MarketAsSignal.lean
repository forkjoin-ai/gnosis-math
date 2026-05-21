import Init

namespace Gnosis
namespace MarketAsSignal

inductive MarketVenue where
  | publicMarket
  | phylePrivate
  | internal
  deriving Repr, DecidableEq

structure MarketObservation where
  venue : MarketVenue
  price : Nat
  liquidity : Nat
  deriving Repr, DecidableEq

def validObservation (m : MarketObservation) : Prop :=
  m.price ≤ 100 ∧ m.liquidity ≤ 100

def isSignal (_m : MarketObservation) : Prop := True

def withVenue (m : MarketObservation) (venue : MarketVenue) : MarketObservation :=
  { m with venue := venue }

theorem market_observation_is_signal (m : MarketObservation) :
    isSignal m := by
  constructor

theorem valid_market_price_bounded (m : MarketObservation)
    (h : validObservation m) : m.price ≤ 100 := h.left

theorem valid_market_liquidity_bounded (m : MarketObservation)
    (h : validObservation m) : m.liquidity ≤ 100 := h.right

theorem venue_change_preserves_valid_observation
    (m : MarketObservation) (venue : MarketVenue)
    (h : validObservation m) :
    validObservation (withVenue m venue) := by
  dsimp [validObservation, withVenue]
  exact h

theorem venue_change_preserves_signal
    (m : MarketObservation) (venue : MarketVenue) :
    isSignal (withVenue m venue) := by
  exact market_observation_is_signal (withVenue m venue)

theorem public_private_internal_share_validity
    (m : MarketObservation)
    (h : validObservation m) :
    validObservation (withVenue m MarketVenue.publicMarket) ∧
    validObservation (withVenue m MarketVenue.phylePrivate) ∧
    validObservation (withVenue m MarketVenue.internal) := by
  constructor
  · exact venue_change_preserves_valid_observation m MarketVenue.publicMarket h
  · constructor
    · exact venue_change_preserves_valid_observation m MarketVenue.phylePrivate h
    · exact venue_change_preserves_valid_observation m MarketVenue.internal h

end MarketAsSignal
end Gnosis
