namespace BuleyeanMath

structure HolographicPluralistEntropy where
  holographic_bound : Nat
  pluralist_entropy : Nat

theorem pluralist_entropy_bounded_by_holography (e : HolographicPluralistEntropy) (h : e.pluralist_entropy ≤ e.holographic_bound) :
  e.pluralist_entropy ≤ e.holographic_bound := h

end BuleyeanMath