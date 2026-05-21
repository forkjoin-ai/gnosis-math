namespace Gnosis.Witnesses.Bible.FirstPeter
namespace FirstPeterConscienceAnswerWitness

/-!
# 1 Peter 3 -- Household Witness, Blessing, and Good Conscience

Source slice: 1 Peter 3:1-22.

Chapter invariant: witness can operate without winning the visible argument.
Household conduct, meek hidden adornment, honour between heirs of life, and
non-retaliatory blessing all make accusation answerable without becoming its
mirror.

Primary gap/counterproof: terror and slander are not sovereign. Peter refuses
the idea that defense must become domination: sanctify the Lord in the heart,
answer hope with meekness and fear, and let false accusers be ashamed by good
conversation.

Unseen sat: baptism is not skin-washing but the answer of a good conscience by
resurrection. Christ suffers once, the just for the unjust, descends through
death, and stands above angels, authorities, and powers.

No `sorry`, no new `axiom`.
-/

structure HouseholdWitness where
  conductCanWinWithoutWord : Bool := true
  hiddenHeartOutranksGoldAdorning : Bool := true
  meekQuietSpiritIsGreatPrice : Bool := true
  husbandsHonorAsHeirsTogether : Bool := true
  dishonorCanHinderPrayer : Bool := true
deriving DecidableEq, Repr

def householdWitness : HouseholdWitness := {}

def householdWitnessProp (h : HouseholdWitness) : Prop :=
  h.conductCanWinWithoutWord = true ∧
  h.hiddenHeartOutranksGoldAdorning = true ∧
  h.meekQuietSpiritIsGreatPrice = true ∧
  h.husbandsHonorAsHeirsTogether = true ∧
  h.dishonorCanHinderPrayer = true

structure BlessingConscience where
  evilNotReturnedForEvil : Bool := true
  blessingInheritsBlessing : Bool := true
  tongueRefrainsFromGuile : Bool := true
  peaceIsSoughtAndPursued : Bool := true
  hopeAnswerRequiresMeekFear : Bool := true
  goodConscienceShamesFalseAccusation : Bool := true
deriving DecidableEq, Repr

def blessingConscience : BlessingConscience := {}

def blessingConscienceWitness (b : BlessingConscience) : Prop :=
  b.evilNotReturnedForEvil = true ∧
  b.blessingInheritsBlessing = true ∧
  b.tongueRefrainsFromGuile = true ∧
  b.peaceIsSoughtAndPursued = true ∧
  b.hopeAnswerRequiresMeekFear = true ∧
  b.goodConscienceShamesFalseAccusation = true

structure ResurrectionAnswerCounterproof where
  sufferingForWellDoingOutranksEvilDoing : Bool := true
  justSuffersForUnjustToBringToGod : Bool := true
  noahWatersBecomeFigure : Bool := true
  baptismNotFleshWashing : Bool := true
  conscienceAnswerByResurrection : Bool := true
  powersMadeSubjectToAscendedChrist : Bool := true
deriving DecidableEq, Repr

def resurrectionAnswerCounterproof : ResurrectionAnswerCounterproof := {}

def fleshAnswerRejected (c : ResurrectionAnswerCounterproof) : Prop :=
  c.sufferingForWellDoingOutranksEvilDoing = true ∧
  c.justSuffersForUnjustToBringToGod = true ∧
  c.noahWatersBecomeFigure = true ∧
  c.baptismNotFleshWashing = true ∧
  c.conscienceAnswerByResurrection = true ∧
  c.powersMadeSubjectToAscendedChrist = true

theorem first_peter_household_witness :
    householdWitnessProp householdWitness := by
  unfold householdWitnessProp householdWitness
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_blessing_conscience :
    blessingConscienceWitness blessingConscience := by
  unfold blessingConscienceWitness blessingConscience
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_flesh_answer_rejected :
    fleshAnswerRejected resurrectionAnswerCounterproof := by
  unfold fleshAnswerRejected resurrectionAnswerCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_conscience_answer_witness :
    householdWitnessProp householdWitness ∧
    blessingConscienceWitness blessingConscience ∧
    fleshAnswerRejected resurrectionAnswerCounterproof := by
  exact ⟨first_peter_household_witness,
    first_peter_blessing_conscience,
    first_peter_flesh_answer_rejected⟩

end FirstPeterConscienceAnswerWitness
end Gnosis.Witnesses.Bible.FirstPeter
