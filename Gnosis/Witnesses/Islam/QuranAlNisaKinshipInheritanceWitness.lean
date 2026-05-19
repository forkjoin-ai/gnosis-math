import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaKinshipInheritanceWitness

/-!
# Quran 4:1-14, An-Nisa -- Kinship, Orphans, Marriage Fairness, and Inheritance Bounds

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2753-2838`.

This bounded witness tracks the opening legal and ethical unit of Sura 4:

  * people are told to be mindful of the Lord who created them from a single soul,
    its mate, and the many men and women spread from them;
  * God is named as the one in whose name people make requests of one another;
  * kinship ties must not be severed because God is always watching;
  * orphan property must be returned, not exchanged for bad property or consumed
    together with a guardian's own property;
  * marriage permission is bounded by fear of unfairness to orphan girls and by equity;
  * women receive their bridal gifts, while voluntary remission is treated separately;
  * property is a means of support, with provision, clothing, kind address, testing,
    sound judgment, witnessed transfer, and fair guardian restraint;
  * men and women both receive ordained shares from parents and close relatives;
  * relatives, orphans, and needy people present at distribution receive kindness;
  * fear for one's own helpless children becomes a rule for concern toward orphans;
  * unjust consumption of orphan property is figured as swallowing fire;
  * child, parent, spouse, and sibling inheritance shares are given after bequests or debts;
  * these rulings are called God's bounds, with obedience leading to Gardens and
    overstepping leading to humiliating torment.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive KinshipInheritanceMoment
  | singleSoulOrigin
  | kinshipWatchfulness
  | orphanPropertyReturned
  | marriageFairnessBound
  | bridalGift
  | propertySupportAndTesting
  | witnessedTransfer
  | menWomenShares
  | distributionKindness
  | helplessChildrenConcern
  | orphanPropertyFire
  | inheritanceShares
  | bequestsDebtsBoundary
  | godsBounds
deriving DecidableEq, Repr

def kinshipInheritanceMoments : List KinshipInheritanceMoment :=
  [ KinshipInheritanceMoment.singleSoulOrigin
  , KinshipInheritanceMoment.kinshipWatchfulness
  , KinshipInheritanceMoment.orphanPropertyReturned
  , KinshipInheritanceMoment.marriageFairnessBound
  , KinshipInheritanceMoment.bridalGift
  , KinshipInheritanceMoment.propertySupportAndTesting
  , KinshipInheritanceMoment.witnessedTransfer
  , KinshipInheritanceMoment.menWomenShares
  , KinshipInheritanceMoment.distributionKindness
  , KinshipInheritanceMoment.helplessChildrenConcern
  , KinshipInheritanceMoment.orphanPropertyFire
  , KinshipInheritanceMoment.inheritanceShares
  , KinshipInheritanceMoment.bequestsDebtsBoundary
  , KinshipInheritanceMoment.godsBounds
  ]

structure KinshipInheritancePattern where
  singleSoulCreationNamed : Bool
  mateCreatedFromIt : Bool
  manyMenWomenSpread : Bool
  kinshipTiesProtected : Bool
  godAlwaysWatching : Bool
  orphanPropertyProtected : Bool
  propertyExchangeCondemned : Bool
  marriageEquityBound : Bool
  bridalGiftGiven : Bool
  propertyMeansSupport : Bool
  orphansTestedForJudgment : Bool
  transferWitnessed : Bool
  menAndWomenReceiveShares : Bool
  needyPresentReceiveKindness : Bool
  unjustOrphanConsumptionFire : Bool
  bequestsDebtsPrior : Bool
  godsBoundsNamed : Bool
  obedienceGardens : Bool
  oversteppingFire : Bool
deriving DecidableEq, Repr

def kinshipInheritancePattern : KinshipInheritancePattern where
  singleSoulCreationNamed := true
  mateCreatedFromIt := true
  manyMenWomenSpread := true
  kinshipTiesProtected := true
  godAlwaysWatching := true
  orphanPropertyProtected := true
  propertyExchangeCondemned := true
  marriageEquityBound := true
  bridalGiftGiven := true
  propertyMeansSupport := true
  orphansTestedForJudgment := true
  transferWitnessed := true
  menAndWomenReceiveShares := true
  needyPresentReceiveKindness := true
  unjustOrphanConsumptionFire := true
  bequestsDebtsPrior := true
  godsBoundsNamed := true
  obedienceGardens := true
  oversteppingFire := true

theorem quran_al_nisa_kinship_inheritance_witness :
    kinshipInheritanceMoments.length = 14
    ∧ kinshipInheritanceMoments.head? = some KinshipInheritanceMoment.singleSoulOrigin
    ∧ kinshipInheritanceMoments.getLast? = some KinshipInheritanceMoment.godsBounds
    ∧ kinshipInheritancePattern.singleSoulCreationNamed = true
    ∧ kinshipInheritancePattern.mateCreatedFromIt = true
    ∧ kinshipInheritancePattern.manyMenWomenSpread = true
    ∧ kinshipInheritancePattern.kinshipTiesProtected = true
    ∧ kinshipInheritancePattern.godAlwaysWatching = true
    ∧ kinshipInheritancePattern.orphanPropertyProtected = true
    ∧ kinshipInheritancePattern.propertyExchangeCondemned = true
    ∧ kinshipInheritancePattern.marriageEquityBound = true
    ∧ kinshipInheritancePattern.bridalGiftGiven = true
    ∧ kinshipInheritancePattern.propertyMeansSupport = true
    ∧ kinshipInheritancePattern.orphansTestedForJudgment = true
    ∧ kinshipInheritancePattern.transferWitnessed = true
    ∧ kinshipInheritancePattern.menAndWomenReceiveShares = true
    ∧ kinshipInheritancePattern.needyPresentReceiveKindness = true
    ∧ kinshipInheritancePattern.unjustOrphanConsumptionFire = true
    ∧ kinshipInheritancePattern.bequestsDebtsPrior = true
    ∧ kinshipInheritancePattern.godsBoundsNamed = true
    ∧ kinshipInheritancePattern.obedienceGardens = true
    ∧ kinshipInheritancePattern.oversteppingFire = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaKinshipInheritanceWitness
end Gnosis.Witnesses.Islam
