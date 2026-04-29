namespace MoonshotGossipEntropy

structure GossipProtocol where
  node_count : Nat
  entropy : Nat
  entropy_bound : entropy ≤ node_count

theorem gossip_entropy_bounded (g : GossipProtocol) :
  g.entropy ≤ g.node_count := by
  exact g.entropy_bound

end MoonshotGossipEntropy