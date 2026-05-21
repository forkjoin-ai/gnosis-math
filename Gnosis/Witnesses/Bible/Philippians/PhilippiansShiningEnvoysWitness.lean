import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansShiningEnvoysWitness

/-!
# Philippians 2:12-30 -- Work Out, Shine, and Receive Proven Envoys

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94477-94520`.

God works in the willing and doing; the community shines by refusing murmuring
and holding the word of life. Timothy and Epaphroditus then embody care, proof,
risk, mercy, and service.

No `sorry`, no new `axiom`.
-/

structure ShiningObedience where
  salvationWorkedOutFearTrembling : Bool := true
  godWorksWillAndDo : Bool := true
  murmuringsDisputingsRejected : Bool := true
  blamelessHarmlessLights : Bool := true
  wordOfLifeHeldForth : Bool := true
  sacrificeServiceJoy : Bool := true
deriving DecidableEq, Repr

def shiningObedience : ShiningObedience := {}

def shiningObedienceWitness (s : ShiningObedience) : Prop :=
  s.salvationWorkedOutFearTrembling = true ∧ s.godWorksWillAndDo = true ∧
  s.murmuringsDisputingsRejected = true ∧ s.blamelessHarmlessLights = true ∧
  s.wordOfLifeHeldForth = true ∧ s.sacrificeServiceJoy = true

structure ProvenEnvoys where
  timothyLikemindedCare : Bool := true
  othersSeekOwnThings : Bool := true
  timothyProofAsSon : Bool := true
  epaphroditusBrotherFellowsoldier : Bool := true
  sicknessNighDeathMercy : Bool := true
  receiveWithGladnessReputation : Bool := true
  riskedLifeForWorkOfChrist : Bool := true
deriving DecidableEq, Repr

def provenEnvoys : ProvenEnvoys := {}

def provenEnvoysWitness (e : ProvenEnvoys) : Prop :=
  e.timothyLikemindedCare = true ∧ e.othersSeekOwnThings = true ∧
  e.timothyProofAsSon = true ∧ e.epaphroditusBrotherFellowsoldier = true ∧
  e.sicknessNighDeathMercy = true ∧ e.receiveWithGladnessReputation = true ∧
  e.riskedLifeForWorkOfChrist = true

theorem philippians_shining_obedience :
    shiningObedienceWitness shiningObedience := by
  unfold shiningObedienceWitness shiningObedience
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_proven_envoys :
    provenEnvoysWitness provenEnvoys := by
  unfold provenEnvoysWitness provenEnvoys
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_shining_envoys_witness :
    shiningObedienceWitness shiningObedience ∧ provenEnvoysWitness provenEnvoys := by
  exact ⟨philippians_shining_obedience, philippians_proven_envoys⟩

end PhilippiansShiningEnvoysWitness
end Gnosis.Witnesses.Bible.Philippians
