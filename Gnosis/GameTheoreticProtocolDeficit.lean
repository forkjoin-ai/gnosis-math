namespace Gnosis

def protocolDeficit (paths streams : Nat) : Nat :=
  paths - streams

def priceOfAnarchyNash (selfishCost optimalCost : Nat) : Nat :=
  selfishCost - optimalCost

theorem game_theoretic_protocol_isomorphism (paths streams selfish optimal : Nat)
    (hPaths : paths = selfish)
    (hStreams : streams = optimal)
    (_hValid : paths >= streams) :
    protocolDeficit paths streams = priceOfAnarchyNash selfish optimal := by
  unfold protocolDeficit priceOfAnarchyNash
  exact hPaths ▸ hStreams ▸ rfl

end Gnosis