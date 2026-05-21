namespace Gnosis.Witnesses.Bible.James
namespace JamesPartialityWorksWitness

/-!
# James 2 -- Partiality, Mercy, and Faith With a Body

Source slice: James 2:1-26.

Chapter invariant: the faith of the Lord of glory cannot coexist with ranking
persons by visible status. The assembly's seating chart is already a theology:
honoring the gold ring while lowering the poor turns worship into evil judgment.

Primary gap/counterproof: speech can bless without feeding, and belief can
tremble without obeying. James refuses both as corpse-religion. A naked and
hungry sibling is not helped by verbal peace; the body of faith is works.

Unseen sat: mercy is not softness after judgment; mercy rejoices against
judgment because it knows the royal law's center. Abraham and Rahab are not
decorations for doctrine; they witness that living faith becomes costly action.

No `sorry`, no new `axiom`.
-/

structure PartialityJudgment where
  gloryFaithRejectsRespectOfPersons : Bool := true
  goldRingSeatingExposesEvilThoughts : Bool := true
  poorCanBeRichInFaithAndKingdomHeirs : Bool := true
  richOppressionCannotDefineHonor : Bool := true
  royalLawRequiresNeighborLove : Bool := true
deriving DecidableEq, Repr

def partialityJudgment : PartialityJudgment := {}

def partialityJudgmentWitness (p : PartialityJudgment) : Prop :=
  p.gloryFaithRejectsRespectOfPersons = true ∧
  p.goldRingSeatingExposesEvilThoughts = true ∧
  p.poorCanBeRichInFaithAndKingdomHeirs = true ∧
  p.richOppressionCannotDefineHonor = true ∧
  p.royalLawRequiresNeighborLove = true

structure MercyLaw where
  onePointOffenseBreaksWholeLaw : Bool := true
  speechAndDoingFaceLibertyLaw : Bool := true
  mercilessJudgmentFallsOnMercilessness : Bool := true
  mercyRejoicesAgainstJudgment : Bool := true
deriving DecidableEq, Repr

def mercyLaw : MercyLaw := {}

def mercyLawWitness (m : MercyLaw) : Prop :=
  m.onePointOffenseBreaksWholeLaw = true ∧
  m.speechAndDoingFaceLibertyLaw = true ∧
  m.mercilessJudgmentFallsOnMercilessness = true ∧
  m.mercyRejoicesAgainstJudgment = true

structure DeadFaithCounterproof where
  verbalPeaceDoesNotWarmOrFill : Bool := true
  faithAloneIsDead : Bool := true
  worksShowFaithsBody : Bool := true
  demonsBelieveAndTremble : Bool := true
  abrahamFaithPerfectedByWorks : Bool := true
  rahabWorksReceiveAndSend : Bool := true
  bodyWithoutSpiritAnalogyClosesCase : Bool := true
deriving DecidableEq, Repr

def deadFaithCounterproof : DeadFaithCounterproof := {}

def corpseFaithRejected (c : DeadFaithCounterproof) : Prop :=
  c.verbalPeaceDoesNotWarmOrFill = true ∧
  c.faithAloneIsDead = true ∧
  c.worksShowFaithsBody = true ∧
  c.demonsBelieveAndTremble = true ∧
  c.abrahamFaithPerfectedByWorks = true ∧
  c.rahabWorksReceiveAndSend = true ∧
  c.bodyWithoutSpiritAnalogyClosesCase = true

theorem james_partiality_judgment :
    partialityJudgmentWitness partialityJudgment := by
  unfold partialityJudgmentWitness partialityJudgment
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem james_mercy_law :
    mercyLawWitness mercyLaw := by
  unfold mercyLawWitness mercyLaw
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem james_corpse_faith_rejected :
    corpseFaithRejected deadFaithCounterproof := by
  unfold corpseFaithRejected deadFaithCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem james_partiality_works_witness :
    partialityJudgmentWitness partialityJudgment ∧
    mercyLawWitness mercyLaw ∧
    corpseFaithRejected deadFaithCounterproof := by
  exact ⟨james_partiality_judgment,
    james_mercy_law,
    james_corpse_faith_rejected⟩

end JamesPartialityWorksWitness
end Gnosis.Witnesses.Bible.James
