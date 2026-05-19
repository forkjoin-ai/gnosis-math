import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace TripartiteHumanityTheologiesWitness

/-!
# Tripartite Tractate -- Mixed Humanity and Confused Theologies

Source text: `docs/ebooks/source-texts/tripartite-tractate.txt`;
text anchor `docs/ebooks/source-texts/tripartite-tractate.txt:836-1113`.

Sat/unseen reading:

Humanity is mixed: left, right, and spiritual word all contribute to a threefold
garden and a divided attention. Death is defined as complete ignorance of the
Totality, while eternal life is firm knowledge of the Totalities. The later
survey of theologies is not neutral doxography; it is an error ledger showing
how partial observation produces incompatible theories.

Gap / counterproof:

Greek, barbarian, Hebrew, prophetic, angelic, and archonic explanations all
become unstable when they mistake a partial power or visible element for the
Totality. The Savior reveals fruits and types.

No `sorry`, no new `axiom`.
-/

structure MixedHumanity where
  shadowEarthlyMan : Bool
  livingSpiritGivesLife : Bool
  deadIsIgnorance : Bool
  spiritualPsychicMaterial : Bool
  firstHumanMixedDeposit : Bool
  threefoldGarden : Bool
deriving DecidableEq, Repr

def tripartiteMixedHumanity : MixedHumanity where
  shadowEarthlyMan := true
  livingSpiritGivesLife := true
  deadIsIgnorance := true
  spiritualPsychicMaterial := true
  firstHumanMixedDeposit := true
  threefoldGarden := true

def humanityIsMixedPedagogy (h : MixedHumanity) : Prop :=
  h.shadowEarthlyMan = true ∧
  h.livingSpiritGivesLife = true ∧
  h.deadIsIgnorance = true ∧
  h.spiritualPsychicMaterial = true ∧
  h.firstHumanMixedDeposit = true ∧
  h.threefoldGarden = true

structure DeathLifeDefinition where
  deathCompleteIgnorance : Bool
  deathRulesAfterTransgression : Bool
  evilExperiencedForTime : Bool
  lifeFirmKnowledge : Bool
  greatestGoodReceived : Bool
deriving DecidableEq, Repr

def tripartiteDeathLifeDefinition : DeathLifeDefinition where
  deathCompleteIgnorance := true
  deathRulesAfterTransgression := true
  evilExperiencedForTime := true
  lifeFirmKnowledge := true
  greatestGoodReceived := true

def deathLifeAreKnowledgeIndexed (d : DeathLifeDefinition) : Prop :=
  d.deathCompleteIgnorance = true ∧
  d.deathRulesAfterTransgression = true ∧
  d.evilExperiencedForTime = true ∧
  d.lifeFirmKnowledge = true ∧
  d.greatestGoodReceived = true

structure TheologyErrorLedger where
  providenceOnlyPartial : Bool
  alienOnlyPartial : Bool
  destinyNatureSelfExistentPartial : Bool
  visibleElementsLimit : Bool
  philosophiesDisagree : Bool
  propheticUnityNeedsSavior : Bool
deriving DecidableEq, Repr

def tripartiteTheologyErrorLedger : TheologyErrorLedger where
  providenceOnlyPartial := true
  alienOnlyPartial := true
  destinyNatureSelfExistentPartial := true
  visibleElementsLimit := true
  philosophiesDisagree := true
  propheticUnityNeedsSavior := true

def partialTheologiesAreCounterproofs (t : TheologyErrorLedger) : Prop :=
  t.providenceOnlyPartial = true ∧
  t.alienOnlyPartial = true ∧
  t.destinyNatureSelfExistentPartial = true ∧
  t.visibleElementsLimit = true ∧
  t.philosophiesDisagree = true ∧
  t.propheticUnityNeedsSavior = true

structure TripartitionRevealed where
  typesKnownByFruit : Bool
  revealedAtSaviorComing : Bool
  spiritualRunsToHead : Bool
  psychicHesitatesByVoice : Bool
  materialShunsLight : Bool
  humilityPathToRest : Bool
deriving DecidableEq, Repr

def tripartiteTripartitionRevealed : TripartitionRevealed where
  typesKnownByFruit := true
  revealedAtSaviorComing := true
  spiritualRunsToHead := true
  psychicHesitatesByVoice := true
  materialShunsLight := true
  humilityPathToRest := true

def saviorRevealsFruitTypes (r : TripartitionRevealed) : Prop :=
  r.typesKnownByFruit = true ∧
  r.revealedAtSaviorComing = true ∧
  r.spiritualRunsToHead = true ∧
  r.psychicHesitatesByVoice = true ∧
  r.materialShunsLight = true ∧
  r.humilityPathToRest = true

theorem tripartite_humanity_mixed :
    humanityIsMixedPedagogy tripartiteMixedHumanity := by
  unfold humanityIsMixedPedagogy tripartiteMixedHumanity
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_death_life_knowledge :
    deathLifeAreKnowledgeIndexed tripartiteDeathLifeDefinition := by
  unfold deathLifeAreKnowledgeIndexed tripartiteDeathLifeDefinition
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_partial_theology_counterproof :
    partialTheologiesAreCounterproofs tripartiteTheologyErrorLedger := by
  unfold partialTheologiesAreCounterproofs tripartiteTheologyErrorLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_savior_reveals_types :
    saviorRevealsFruitTypes tripartiteTripartitionRevealed := by
  unfold saviorRevealsFruitTypes tripartiteTripartitionRevealed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_human_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem tripartite_humanity_theologies_witness :
    humanityIsMixedPedagogy tripartiteMixedHumanity ∧
    deathLifeAreKnowledgeIndexed tripartiteDeathLifeDefinition ∧
    partialTheologiesAreCounterproofs tripartiteTheologyErrorLedger ∧
    saviorRevealsFruitTypes tripartiteTripartitionRevealed ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨tripartite_humanity_mixed,
    tripartite_death_life_knowledge,
    tripartite_partial_theology_counterproof,
    tripartite_savior_reveals_types,
    tripartite_human_recovery_shape⟩

end TripartiteHumanityTheologiesWitness
end Gnosis.Witnesses.Gnostic
