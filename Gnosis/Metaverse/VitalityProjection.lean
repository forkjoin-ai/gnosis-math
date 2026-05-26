import Gnosis.ConsciousnessVsObjectivity
import Gnosis.Body.TwoVitalities
import Gnosis.MycelialEmergenceGraph

namespace Gnosis
namespace Metaverse

/-!
# Metaverse vitality projection

The metaverse object surface uses "animacy" operationally: every shape carries a
vitality/payoff surface. This module pins that surface to the existing Gnosis
definition of vitality as the positive knowledge derivative.
-/

def knowledgeYesterday (k : KnowledgeTrajectory) (t : Nat) : Nat :=
  k t

def knowledgeToday (k : KnowledgeTrajectory) (t : Nat) : Nat :=
  k (t + 1)

def knowledgeGain (k : KnowledgeTrajectory) (t : Nat) : Nat :=
  knowledgeToday k t - knowledgeYesterday k t

def knowledgeLoss (k : KnowledgeTrajectory) (t : Nat) : Nat :=
  knowledgeYesterday k t - knowledgeToday k t

def animacyVitality (k : KnowledgeTrajectory) (t : Nat) : Nat :=
  knowledgeGain k t

structure MetaverseVitalitySurface where
  momentaryLiving : Nat
  persistedAlive : Nat
deriving DecidableEq, Repr

def metaverseVitalitySurface
    (k : KnowledgeTrajectory)
    (t carriedCycles : Nat) : MetaverseVitalitySurface :=
  { momentaryLiving := animacyVitality k t
  , persistedAlive := k (t + carriedCycles + 1) - k t }

theorem animacy_vitality_matches_gnosis_vitality
    (k : KnowledgeTrajectory) (t : Nat) :
    animacyVitality k t = vitality k t := by
  rfl

theorem knowledge_gain_is_today_minus_yesterday
    (k : KnowledgeTrajectory) (t : Nat) :
    knowledgeGain k t = knowledgeToday k t - knowledgeYesterday k t := by
  rfl

theorem objective_shape_has_zero_animacy_vitality
    {M : Nat} {k : KnowledgeTrajectory}
    (hObjective : ObjectiveTrajectory M k) :
    ∀ t, animacyVitality k t = 0 := by
  intro t
  exact objectivity_has_zero_vitality hObjective t

theorem metaverse_surface_momentary_matches_animacy_vitality
    (k : KnowledgeTrajectory) (t carriedCycles : Nat) :
    (metaverseVitalitySurface k t carriedCycles).momentaryLiving =
      animacyVitality k t := by
  rfl

theorem metaverse_surface_zero_carried_cycles_is_momentary
    (k : KnowledgeTrajectory) (t : Nat) :
    (metaverseVitalitySurface k t 0).persistedAlive =
      animacyVitality k t := by
  unfold metaverseVitalitySurface animacyVitality knowledgeGain
  rfl

def mycelialVitalityNode
    (phyleIndex persistedAlive : Nat) :
    MycelialEmergenceGraph.EmergenceNode :=
  { phyleIndex := phyleIndex, trust := persistedAlive }

def mycelialAttentionEdge
    (source target affinity chaosDisagreement : Nat) :
    MycelialEmergenceGraph.EmergenceEdge :=
  { source := source
  , target := target
  , affinity := affinity
  , disagreement := chaosDisagreement }

theorem mycelial_attention_routes_when_vitality_exceeds_chaos
    (source target vitality chaos : Nat)
    (h : chaos < vitality) :
    MycelialEmergenceGraph.coalitionCandidate
      (mycelialAttentionEdge source target vitality chaos) := by
  exact h

def mycelialAttentionWeight
    (persistedAlive agency chaosPressure : Nat) : Nat :=
  persistedAlive * (agency + 1) * (chaosPressure + 1)

theorem mycelial_attention_weight_monotone_in_persisted_vitality
    {leftAlive rightAlive agency chaosPressure : Nat}
    (hAlive : leftAlive ≤ rightAlive) :
    mycelialAttentionWeight leftAlive agency chaosPressure ≤
      mycelialAttentionWeight rightAlive agency chaosPressure := by
  unfold mycelialAttentionWeight
  exact Nat.mul_le_mul_right (chaosPressure + 1)
    (Nat.mul_le_mul_right (agency + 1) hAlive)

theorem mycelial_attention_weight_monotone_in_agency
    {alive leftAgency rightAgency chaosPressure : Nat}
    (hAgency : leftAgency ≤ rightAgency) :
    mycelialAttentionWeight alive leftAgency chaosPressure ≤
      mycelialAttentionWeight alive rightAgency chaosPressure := by
  unfold mycelialAttentionWeight
  exact Nat.mul_le_mul_right (chaosPressure + 1)
    (Nat.mul_le_mul_left alive (Nat.succ_le_succ hAgency))

theorem mycelial_attention_weight_monotone_in_chaos_pressure
    {alive agency leftChaos rightChaos : Nat}
    (hChaos : leftChaos ≤ rightChaos) :
    mycelialAttentionWeight alive agency leftChaos ≤
      mycelialAttentionWeight alive agency rightChaos := by
  unfold mycelialAttentionWeight
  exact Nat.mul_le_mul_left (alive * (agency + 1)) (Nat.succ_le_succ hChaos)

end Metaverse
end Gnosis
