import Init

namespace Gnosis
namespace MycelialEmergenceGraph

structure EmergenceNode where
  phyleIndex : Nat
  trust : Nat
  deriving Repr, DecidableEq

structure EmergenceEdge where
  source : Nat
  target : Nat
  affinity : Nat
  disagreement : Nat
  deriving Repr, DecidableEq

def validNode (n : EmergenceNode) : Prop := n.trust ≤ 100

def validEdge (e : EmergenceEdge) : Prop :=
  e.affinity ≤ 100 ∧ e.disagreement ≤ 100

def coalitionCandidate (e : EmergenceEdge) : Prop :=
  e.affinity > e.disagreement

def withDisagreement (e : EmergenceEdge) (newDisagreement : Nat) : EmergenceEdge :=
  { e with disagreement := newDisagreement }

theorem valid_node_trust_bounded (n : EmergenceNode) (h : validNode n) :
    n.trust ≤ 100 := h

theorem valid_edge_affinity_bounded (e : EmergenceEdge) (h : validEdge e) :
    e.affinity ≤ 100 := h.left

theorem valid_edge_disagreement_bounded (e : EmergenceEdge) (h : validEdge e) :
    e.disagreement ≤ 100 := h.right

theorem coalition_affinity_exceeds_disagreement (e : EmergenceEdge)
    (h : coalitionCandidate e) : e.disagreement < e.affinity := h

theorem coalition_candidate_preserved_by_lower_disagreement
    (e : EmergenceEdge) (newDisagreement : Nat)
    (hCoalition : coalitionCandidate e)
    (hLower : newDisagreement ≤ e.disagreement) :
    coalitionCandidate (withDisagreement e newDisagreement) := by
  dsimp [coalitionCandidate, withDisagreement]
  exact Nat.lt_of_le_of_lt hLower hCoalition

end MycelialEmergenceGraph
end Gnosis
