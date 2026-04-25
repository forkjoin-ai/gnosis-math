import Init

namespace Gnosis

/-!
# Ant Colony Collective Intelligence (Sketch)

Sketch surface linking:
1. reproductive-void caste structure,
2. fork/race/fold resource accounting,
3. propagation/community signals, and
4. cross-system intelligence classification equivalence conditions.

This is intentionally a minimal formal scaffold for iterative refinement.
-/

structure FRFProfile where
  fork : Nat
  race : Nat
  fold : Nat
  vent : Nat

def FRFProfile.resourceBudget (p : FRFProfile) : Nat :=
  p.fork + p.race + p.fold

def FRFProfile.propagationPotential (p : FRFProfile) : Nat :=
  p.fork + p.race

def FRFProfile.communityPotential (p : FRFProfile) : Nat :=
  p.race + p.fold

def FRFProfile.stabilitySignal (p : FRFProfile) : Nat :=
  p.propagationPotential + p.communityPotential

def FRFProfile.stabilityWeight (p : FRFProfile) : Nat :=
  p.resourceBudget - Nat.min p.vent p.resourceBudget + 1

theorem stability_weight_positive (p : FRFProfile) :
    0 < p.stabilityWeight := by
  unfold FRFProfile.stabilityWeight
  exact Nat.succ_pos _

theorem stability_signal_eq_resource_plus_race (p : FRFProfile) :
    p.stabilitySignal = p.resourceBudget + p.race := by
  unfold FRFProfile.stabilitySignal FRFProfile.propagationPotential
    FRFProfile.communityPotential FRFProfile.resourceBudget
  simp [Nat.add_left_comm, Nat.add_comm]

theorem stability_weight_le_resource_plus_one (p : FRFProfile) :
    p.stabilityWeight ≤ p.resourceBudget + 1 := by
  unfold FRFProfile.stabilityWeight
  have hsub : p.resourceBudget - Nat.min p.vent p.resourceBudget ≤ p.resourceBudget :=
    Nat.sub_le _ _
  exact Nat.succ_le_succ hsub

structure IntelligenceClassifier where
  bucket : Nat
  bucket_pos : 0 < bucket

def IntelligenceClassifier.classify (c : IntelligenceClassifier) (p : FRFProfile) : Nat :=
  p.stabilityWeight / c.bucket

theorem classify_eq_of_equal_weight (c : IntelligenceClassifier) {p q : FRFProfile}
    (h : p.stabilityWeight = q.stabilityWeight) :
    c.classify p = c.classify q := by
  unfold IntelligenceClassifier.classify
  rw [h]

theorem stability_weight_eq_of_budget_and_vent_eq {p q : FRFProfile}
    (hBudget : p.resourceBudget = q.resourceBudget)
    (hVent : p.vent = q.vent) :
    p.stabilityWeight = q.stabilityWeight := by
  unfold FRFProfile.stabilityWeight
  rw [hBudget, hVent]

structure AntColony where
  breeders : Nat
  reproductiveVoid : Nat
  scouts : Nat
  ventBurden : Nat

def AntColony.toFRF (a : AntColony) : FRFProfile where
  fork := a.breeders + a.reproductiveVoid
  race := a.reproductiveVoid + a.scouts
  fold := a.breeders
  vent := a.ventBurden

def AntColony.withExtraVoid (a : AntColony) (k : Nat) : AntColony :=
  { a with reproductiveVoid := a.reproductiveVoid + k }

theorem extra_void_increases_race (a : AntColony) (k : Nat) :
    (a.withExtraVoid k).toFRF.race = a.toFRF.race + k := by
  unfold AntColony.withExtraVoid AntColony.toFRF
  simp [Nat.add_left_comm, Nat.add_comm]

theorem extra_void_increases_stability_signal (a : AntColony) (k : Nat) :
    ((a.withExtraVoid k).toFRF).stabilitySignal =
      (a.toFRF).stabilitySignal + (k + k + k) := by
  unfold FRFProfile.stabilitySignal FRFProfile.propagationPotential
    FRFProfile.communityPotential AntColony.withExtraVoid AntColony.toFRF
  simp [Nat.add_left_comm, Nat.add_comm]

structure BuddingSnapshot where
  parent : AntColony
  daughter : AntColony
  parent_queen_pos : 0 < parent.breeders
  daughter_queen_pos : 0 < daughter.breeders

def BuddingSnapshot.totalBreeders (b : BuddingSnapshot) : Nat :=
  b.parent.breeders + b.daughter.breeders

def BuddingSnapshot.networkProfile (b : BuddingSnapshot) : FRFProfile where
  fork := b.parent.toFRF.fork + b.daughter.toFRF.fork
  race := b.parent.toFRF.race + b.daughter.toFRF.race
  fold := b.parent.toFRF.fold + b.daughter.toFRF.fold
  vent := b.parent.toFRF.vent + b.daughter.toFRF.vent

theorem budding_two_queen_floor (b : BuddingSnapshot) :
    2 ≤ b.totalBreeders := by
  unfold BuddingSnapshot.totalBreeders
  have hParent : 1 ≤ b.parent.breeders := Nat.succ_le_of_lt b.parent_queen_pos
  have hDaughter : 1 ≤ b.daughter.breeders := Nat.succ_le_of_lt b.daughter_queen_pos
  calc
    2 = 1 + 1 := rfl
    _ ≤ b.parent.breeders + b.daughter.breeders := Nat.add_le_add hParent hDaughter

theorem budding_survives_one_queen_loss (b : BuddingSnapshot) :
    0 < b.totalBreeders - 1 := by
  have hfloor : 2 ≤ b.totalBreeders := budding_two_queen_floor b
  have h12 : 1 < 2 := by decide
  exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le h12 hfloor)

theorem budding_network_fork_strictly_exceeds_parent (b : BuddingSnapshot) :
    b.parent.toFRF.fork < b.networkProfile.fork := by
  have hdaughter_fork_pos : 0 < b.daughter.toFRF.fork := by
    have hle : b.daughter.breeders ≤ b.daughter.toFRF.fork := by
      unfold AntColony.toFRF
      exact Nat.le_add_right _ _
    exact Nat.lt_of_lt_of_le b.daughter_queen_pos hle
  unfold BuddingSnapshot.networkProfile
  exact Nat.lt_add_of_pos_right hdaughter_fork_pos

structure HumanCollective where
  reproductiveCore : Nat
  supportLayer : Nat
  explorationLayer : Nat
  ventBurden : Nat

def HumanCollective.toFRF (h : HumanCollective) : FRFProfile where
  fork := h.reproductiveCore + h.supportLayer
  race := h.supportLayer + h.explorationLayer
  fold := h.reproductiveCore
  vent := h.ventBurden

def hiveLevelEquivalent
    (classifier : IntelligenceClassifier)
    (ants : AntColony)
    (humans : HumanCollective) : Prop :=
  classifier.classify ants.toFRF = classifier.classify humans.toFRF

theorem hive_level_equivalent_of_equal_weight
    (classifier : IntelligenceClassifier)
    (ants : AntColony)
    (humans : HumanCollective)
    (hWeight : ants.toFRF.stabilityWeight = humans.toFRF.stabilityWeight) :
    hiveLevelEquivalent classifier ants humans := by
  unfold hiveLevelEquivalent
  exact classify_eq_of_equal_weight classifier hWeight

theorem hive_level_equivalent_of_equal_budget_and_vent
    (classifier : IntelligenceClassifier)
    (ants : AntColony)
    (humans : HumanCollective)
    (hBudget : ants.toFRF.resourceBudget = humans.toFRF.resourceBudget)
    (hVent : ants.toFRF.vent = humans.toFRF.vent) :
    hiveLevelEquivalent classifier ants humans := by
  apply hive_level_equivalent_of_equal_weight
  exact stability_weight_eq_of_budget_and_vent_eq hBudget hVent

/-!
Network bus abstraction for applying fork/race/fold diversity arguments to
`open-source/aeon` style lazy transport surfaces.
-/
structure NetworkProfile where
  forkDiversity : Nat
  raceDiversity : Nat
  foldDiversity : Nat
  voidRelays : Nat
  throughputBase : Nat

def NetworkProfile.diversityIndex (n : NetworkProfile) : Nat :=
  n.forkDiversity + n.raceDiversity + n.foldDiversity

def NetworkProfile.isLowDiversity (n : NetworkProfile) : Prop :=
  n.diversityIndex = 0

def NetworkProfile.nominalEfficiency (n : NetworkProfile) : Nat :=
  n.throughputBase - Nat.min n.diversityIndex n.throughputBase

def NetworkProfile.correlatedFaultResilience (n : NetworkProfile) : Nat :=
  n.diversityIndex + n.voidRelays

def NetworkProfile.withExtraVoidRelays (n : NetworkProfile) (k : Nat) : NetworkProfile :=
  { n with voidRelays := n.voidRelays + k }

theorem nominal_efficiency_le_base (n : NetworkProfile) :
    n.nominalEfficiency ≤ n.throughputBase := by
  unfold NetworkProfile.nominalEfficiency
  exact Nat.sub_le _ _

theorem low_diversity_maximizes_nominal_efficiency
    (n : NetworkProfile)
    (hLow : n.isLowDiversity) :
    n.nominalEfficiency = n.throughputBase := by
  unfold NetworkProfile.isLowDiversity at hLow
  unfold NetworkProfile.nominalEfficiency
  rw [hLow]
  simp

theorem low_diversity_minimizes_resilience_of_equal_void
    {low peer : NetworkProfile}
    (hLow : low.isLowDiversity)
    (hVoid : low.voidRelays = peer.voidRelays) :
    low.correlatedFaultResilience ≤ peer.correlatedFaultResilience := by
  unfold NetworkProfile.isLowDiversity at hLow
  unfold NetworkProfile.correlatedFaultResilience
  rw [hLow, hVoid]
  have hbase : peer.voidRelays ≤ peer.diversityIndex + peer.voidRelays :=
    Nat.le_add_left _ _
  exact (Nat.zero_add _).symm ▸ hbase

theorem low_diversity_resilience_strictly_less_of_diverse_peer
    {low peer : NetworkProfile}
    (hLow : low.isLowDiversity)
    (hVoid : low.voidRelays = peer.voidRelays)
    (hPeerDiv : 0 < peer.diversityIndex) :
    low.correlatedFaultResilience < peer.correlatedFaultResilience := by
  unfold NetworkProfile.isLowDiversity at hLow
  unfold NetworkProfile.correlatedFaultResilience
  rw [hLow, hVoid]
  have hlt : peer.voidRelays < peer.diversityIndex + peer.voidRelays :=
    Nat.lt_add_of_pos_left hPeerDiv
  exact (Nat.zero_add _).symm ▸ hlt

theorem extra_void_relays_increase_resilience (n : NetworkProfile) (k : Nat) :
    (n.withExtraVoidRelays k).correlatedFaultResilience =
      n.correlatedFaultResilience + k := by
  unfold NetworkProfile.withExtraVoidRelays NetworkProfile.correlatedFaultResilience
    NetworkProfile.diversityIndex
  simp [Nat.add_left_comm, Nat.add_comm]

structure ExplorationScenario where
  profile : NetworkProfile
  perturbation : Nat
  correlatedShock : Nat

def ExplorationScenario.laminarGuard (s : ExplorationScenario) : Prop :=
  s.perturbation ≤ s.profile.voidRelays

def ExplorationScenario.shockLoad (s : ExplorationScenario) : Nat :=
  s.perturbation + s.correlatedShock

def ExplorationScenario.stabilityCapacity (s : ExplorationScenario) : Nat :=
  s.profile.correlatedFaultResilience

def ExplorationScenario.isStable (s : ExplorationScenario) : Prop :=
  s.shockLoad ≤ s.stabilityCapacity

theorem exploration_low_diversity_stable_under_laminar
    (s : ExplorationScenario)
    (hLow : s.profile.isLowDiversity)
    (hLaminar : s.laminarGuard)
    (hNoShock : s.correlatedShock = 0) :
    s.isStable := by
  unfold ExplorationScenario.isStable ExplorationScenario.shockLoad
    ExplorationScenario.stabilityCapacity NetworkProfile.correlatedFaultResilience
  unfold ExplorationScenario.laminarGuard at hLaminar
  unfold NetworkProfile.isLowDiversity at hLow
  rw [hNoShock, hLow]
  simpa [Nat.add_zero, Nat.zero_add] using hLaminar

theorem low_diversity_stable_with_positive_shock_requires_void_slack
    (s : ExplorationScenario)
    (hLow : s.profile.isLowDiversity)
    (hShock : 0 < s.correlatedShock)
    (hStable : s.isStable) :
    s.perturbation < s.profile.voidRelays := by
  unfold ExplorationScenario.isStable ExplorationScenario.shockLoad
    ExplorationScenario.stabilityCapacity NetworkProfile.correlatedFaultResilience at hStable
  unfold NetworkProfile.isLowDiversity at hLow
  rw [hLow, Nat.zero_add] at hStable
  have hpert : s.perturbation < s.perturbation + s.correlatedShock :=
    Nat.lt_add_of_pos_right hShock
  exact Nat.lt_of_lt_of_le hpert hStable

theorem exploration_low_diversity_breaks_under_positive_shock_at_capacity
    (s : ExplorationScenario)
    (hLow : s.profile.isLowDiversity)
    (hAtCapacity : s.perturbation = s.profile.voidRelays)
    (hShock : 0 < s.correlatedShock) :
    ¬ s.isStable := by
  have hslack :
      s.isStable → s.perturbation < s.profile.voidRelays := by
    intro hStable
    exact low_diversity_stable_with_positive_shock_requires_void_slack
      s hLow hShock hStable
  intro hStable
  have hstrict := hslack hStable
  rw [hAtCapacity] at hstrict
  exact Nat.lt_irrefl _ hstrict

end Gnosis
