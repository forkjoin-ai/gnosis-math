import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaMessengersJesusInheritanceWitness

/-!
# Quran 4:150-176, An-Nisa -- Messengers, Jesus, Clear Light, and Final Inheritance Ruling

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3347-3440`.

This bounded witness tracks the closing unit of Sura 4:

  * making distinctions among God and His messengers is rejected, while belief without
    distinction receives reward;
  * People of the Book demand a physical book, as earlier demands were made of Moses;
  * calf worship, the raised mountain, the gate command, Sabbath command, and solemn
    pledge are recalled;
  * pledge-breaking, revelation rejection, prophet-killing, claims of closed minds,
    disbelief, and slander against Mary are named;
  * Jesus son of Mary was not killed or crucified, though it appeared so, and God raised
    him to Himself;
  * Jesus will be a witness on Resurrection Day;
  * certain good things were forbidden because of wrongdoing, blocking God's path, usury,
    and wrongful consumption of property;
  * those well grounded in knowledge believe in revelation, prayer, alms, God, and the
    Last Day;
  * revelation to Muhammad is placed with revelation to Noah, Abraham, Ishmael, Isaac,
    Jacob, the Tribes, Jesus, Job, Jonah, Aaron, Solomon, David, Moses, and other messengers;
  * messengers bring good news and warning so people have no excuse before God;
  * God and angels bear witness to what was sent down with knowledge;
  * the Messenger comes with truth, while excess claims about Jesus and Trinity are rejected;
  * Jesus and the angels do not disdain being servants of God;
  * convincing proof and clear light have come, and holding fast brings mercy, favour,
    and straight path;
  * the sura ends with the inheritance ruling for one who dies childless with no surviving
    parents, assigning shares to sister, brother, two sisters, and mixed siblings.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MessengersJesusInheritanceMoment
  | noMessengerDistinction
  | physicalBookDemand
  | mosesPledgeHistory
  | pledgeBreakingAndSlander
  | jesusNotKilledRaised
  | jesusWitness
  | wrongdoingFoodRestriction
  | groundedKnowledgeBelief
  | revelationLine
  | messengersNoExcuse
  | godAngelsWitness
  | truthAndNoExcess
  | servantNotDisdainful
  | clearLightHoldingFast
  | finalInheritanceRuling
deriving DecidableEq, Repr

def messengersJesusInheritanceMoments : List MessengersJesusInheritanceMoment :=
  [ MessengersJesusInheritanceMoment.noMessengerDistinction
  , MessengersJesusInheritanceMoment.physicalBookDemand
  , MessengersJesusInheritanceMoment.mosesPledgeHistory
  , MessengersJesusInheritanceMoment.pledgeBreakingAndSlander
  , MessengersJesusInheritanceMoment.jesusNotKilledRaised
  , MessengersJesusInheritanceMoment.jesusWitness
  , MessengersJesusInheritanceMoment.wrongdoingFoodRestriction
  , MessengersJesusInheritanceMoment.groundedKnowledgeBelief
  , MessengersJesusInheritanceMoment.revelationLine
  , MessengersJesusInheritanceMoment.messengersNoExcuse
  , MessengersJesusInheritanceMoment.godAngelsWitness
  , MessengersJesusInheritanceMoment.truthAndNoExcess
  , MessengersJesusInheritanceMoment.servantNotDisdainful
  , MessengersJesusInheritanceMoment.clearLightHoldingFast
  , MessengersJesusInheritanceMoment.finalInheritanceRuling
  ]

structure MessengersJesusInheritancePattern where
  noDistinctionRewarded : Bool
  mosesDemandRecalled : Bool
  solemnPledgeNamed : Bool
  pledgeBreakingNamed : Bool
  marySlanderNamed : Bool
  jesusNotKilledNorCrucified : Bool
  godRaisedJesus : Bool
  jesusResurrectionWitness : Bool
  usuryAndPropertyWrongNamed : Bool
  groundedKnowledgeBelieve : Bool
  prophetsRevelationListed : Bool
  messengersGoodNewsWarning : Bool
  noExcuseAfterMessengers : Bool
  godAngelsBearWitness : Bool
  trinityExcessRejected : Bool
  servantsOfGodNamed : Bool
  proofClearLightNamed : Bool
  childlessInheritanceClarified : Bool
deriving DecidableEq, Repr

def messengersJesusInheritancePattern : MessengersJesusInheritancePattern where
  noDistinctionRewarded := true
  mosesDemandRecalled := true
  solemnPledgeNamed := true
  pledgeBreakingNamed := true
  marySlanderNamed := true
  jesusNotKilledNorCrucified := true
  godRaisedJesus := true
  jesusResurrectionWitness := true
  usuryAndPropertyWrongNamed := true
  groundedKnowledgeBelieve := true
  prophetsRevelationListed := true
  messengersGoodNewsWarning := true
  noExcuseAfterMessengers := true
  godAngelsBearWitness := true
  trinityExcessRejected := true
  servantsOfGodNamed := true
  proofClearLightNamed := true
  childlessInheritanceClarified := true

theorem quran_al_nisa_messengers_jesus_inheritance_witness :
    messengersJesusInheritanceMoments.length = 15
    ∧ messengersJesusInheritanceMoments.head? = some MessengersJesusInheritanceMoment.noMessengerDistinction
    ∧ messengersJesusInheritanceMoments.getLast? = some MessengersJesusInheritanceMoment.finalInheritanceRuling
    ∧ messengersJesusInheritancePattern.noDistinctionRewarded = true
    ∧ messengersJesusInheritancePattern.mosesDemandRecalled = true
    ∧ messengersJesusInheritancePattern.solemnPledgeNamed = true
    ∧ messengersJesusInheritancePattern.pledgeBreakingNamed = true
    ∧ messengersJesusInheritancePattern.marySlanderNamed = true
    ∧ messengersJesusInheritancePattern.jesusNotKilledNorCrucified = true
    ∧ messengersJesusInheritancePattern.godRaisedJesus = true
    ∧ messengersJesusInheritancePattern.jesusResurrectionWitness = true
    ∧ messengersJesusInheritancePattern.usuryAndPropertyWrongNamed = true
    ∧ messengersJesusInheritancePattern.groundedKnowledgeBelieve = true
    ∧ messengersJesusInheritancePattern.prophetsRevelationListed = true
    ∧ messengersJesusInheritancePattern.messengersGoodNewsWarning = true
    ∧ messengersJesusInheritancePattern.noExcuseAfterMessengers = true
    ∧ messengersJesusInheritancePattern.godAngelsBearWitness = true
    ∧ messengersJesusInheritancePattern.trinityExcessRejected = true
    ∧ messengersJesusInheritancePattern.servantsOfGodNamed = true
    ∧ messengersJesusInheritancePattern.proofClearLightNamed = true
    ∧ messengersJesusInheritancePattern.childlessInheritanceClarified = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaMessengersJesusInheritanceWitness
end Gnosis.Witnesses.Islam
