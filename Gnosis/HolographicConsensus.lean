
namespace Gnosis

structure HolographicConsensusState where
  boundaryInformation : Nat
  bulkConsensus : Nat
  holographic_bound : bulkConsensus ≤ boundaryInformation

theorem holographic_consensus_holds (state : HolographicConsensusState) :
    state.bulkConsensus ≤ state.boundaryInformation := by
  exact state.holographic_bound

end Gnosis