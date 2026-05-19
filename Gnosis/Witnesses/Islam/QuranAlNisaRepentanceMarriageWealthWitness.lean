import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaRepentanceMarriageWealthWitness

/-!
# Quran 4:15-33, An-Nisa -- Repentance, Marriage Bounds, Wealth, and Shares

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2839-2920`.

This bounded witness tracks Quran 4:15-33:

  * lewd conduct is addressed through witnesses, confinement, punishment, repentance,
    and mending;
  * accepted repentance is for evil done in ignorance and followed quickly by repentance;
  * deathbed repentance and defiant death are excluded from true repentance;
  * believers may not inherit women against their will or treat wives harshly to reclaim
    bridal gifts;
  * fair and kind living is commanded even where dislike is felt;
  * replacement of one wife with another does not permit taking back bridal gifts after
    intimacy and solemn pledge;
  * prohibited marriage relations are listed, including paternal wives, close kin,
    milk-relations, in-laws, stepdaughters after consummation, sons' wives, sisters
    simultaneously, and already married women except the named case;
  * lawful marriage seeks wedlock, not fornication, with gifts from property;
  * marriage to believing slave women is bounded by faith, family likeness, consent,
    proper gifts, chastity, and reduced punishment if married;
  * God makes laws clear, guides to righteous ways, turns in mercy, and lightens the
    burden because humanity was created weak;
  * wrongful consumption of wealth is forbidden except trade by mutual consent;
  * killing one another is forbidden, and hostile injustice is answered by Fire;
  * avoiding great sins brings wiping away of minor misdeeds and an honorable entrance;
  * believers are told not to covet unequal gifts but to ask God for bounty;
  * appointed heirs receive what parents, close relatives, and pledged partners leave.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive RepentanceMarriageWealthMoment
  | witnessedLewdness
  | repentanceSoonAfter
  | deathbedRepentanceExcluded
  | noForcedInheritanceOfWomen
  | fairKindLiving
  | bridalGiftNotReclaimed
  | prohibitedMarriageRelations
  | lawfulWedlockGifts
  | believingSlaveMarriageBounds
  | mercyLawClarityBurdenLightened
  | wealthByMutualTrade
  | noKillingOneAnother
  | greatSinsAvoided
  | noCovetingAskBounty
  | appointedHeirsShares
deriving DecidableEq, Repr

def repentanceMarriageWealthMoments : List RepentanceMarriageWealthMoment :=
  [ RepentanceMarriageWealthMoment.witnessedLewdness
  , RepentanceMarriageWealthMoment.repentanceSoonAfter
  , RepentanceMarriageWealthMoment.deathbedRepentanceExcluded
  , RepentanceMarriageWealthMoment.noForcedInheritanceOfWomen
  , RepentanceMarriageWealthMoment.fairKindLiving
  , RepentanceMarriageWealthMoment.bridalGiftNotReclaimed
  , RepentanceMarriageWealthMoment.prohibitedMarriageRelations
  , RepentanceMarriageWealthMoment.lawfulWedlockGifts
  , RepentanceMarriageWealthMoment.believingSlaveMarriageBounds
  , RepentanceMarriageWealthMoment.mercyLawClarityBurdenLightened
  , RepentanceMarriageWealthMoment.wealthByMutualTrade
  , RepentanceMarriageWealthMoment.noKillingOneAnother
  , RepentanceMarriageWealthMoment.greatSinsAvoided
  , RepentanceMarriageWealthMoment.noCovetingAskBounty
  , RepentanceMarriageWealthMoment.appointedHeirsShares
  ]

structure RepentanceMarriageWealthPattern where
  fourWitnessesNamed : Bool
  repentAndMendRelease : Bool
  quickRepentanceAccepted : Bool
  defiantDeathExcluded : Bool
  forcedInheritanceForbidden : Bool
  harshTreatmentForGiftReturnForbidden : Bool
  fairKindLivingCommanded : Bool
  solemnPledgeNamed : Bool
  prohibitedRelationsListed : Bool
  wedlockGiftRequired : Bool
  slaveMarriageConsentGiftChastity : Bool
  lawsMadeClear : Bool
  burdenLightened : Bool
  mutualConsentTrade : Bool
  killingForbidden : Bool
  greatSinsAvoidanceWipesMinor : Bool
  covetingForbiddenBountyAsked : Bool
  appointedHeirsAndShares : Bool
deriving DecidableEq, Repr

def repentanceMarriageWealthPattern : RepentanceMarriageWealthPattern where
  fourWitnessesNamed := true
  repentAndMendRelease := true
  quickRepentanceAccepted := true
  defiantDeathExcluded := true
  forcedInheritanceForbidden := true
  harshTreatmentForGiftReturnForbidden := true
  fairKindLivingCommanded := true
  solemnPledgeNamed := true
  prohibitedRelationsListed := true
  wedlockGiftRequired := true
  slaveMarriageConsentGiftChastity := true
  lawsMadeClear := true
  burdenLightened := true
  mutualConsentTrade := true
  killingForbidden := true
  greatSinsAvoidanceWipesMinor := true
  covetingForbiddenBountyAsked := true
  appointedHeirsAndShares := true

theorem quran_al_nisa_repentance_marriage_wealth_witness :
    repentanceMarriageWealthMoments.length = 15
    ∧ repentanceMarriageWealthMoments.head? = some RepentanceMarriageWealthMoment.witnessedLewdness
    ∧ repentanceMarriageWealthMoments.getLast? = some RepentanceMarriageWealthMoment.appointedHeirsShares
    ∧ repentanceMarriageWealthPattern.fourWitnessesNamed = true
    ∧ repentanceMarriageWealthPattern.repentAndMendRelease = true
    ∧ repentanceMarriageWealthPattern.quickRepentanceAccepted = true
    ∧ repentanceMarriageWealthPattern.defiantDeathExcluded = true
    ∧ repentanceMarriageWealthPattern.forcedInheritanceForbidden = true
    ∧ repentanceMarriageWealthPattern.harshTreatmentForGiftReturnForbidden = true
    ∧ repentanceMarriageWealthPattern.fairKindLivingCommanded = true
    ∧ repentanceMarriageWealthPattern.solemnPledgeNamed = true
    ∧ repentanceMarriageWealthPattern.prohibitedRelationsListed = true
    ∧ repentanceMarriageWealthPattern.wedlockGiftRequired = true
    ∧ repentanceMarriageWealthPattern.slaveMarriageConsentGiftChastity = true
    ∧ repentanceMarriageWealthPattern.lawsMadeClear = true
    ∧ repentanceMarriageWealthPattern.burdenLightened = true
    ∧ repentanceMarriageWealthPattern.mutualConsentTrade = true
    ∧ repentanceMarriageWealthPattern.killingForbidden = true
    ∧ repentanceMarriageWealthPattern.greatSinsAvoidanceWipesMinor = true
    ∧ repentanceMarriageWealthPattern.covetingForbiddenBountyAsked = true
    ∧ repentanceMarriageWealthPattern.appointedHeirsAndShares = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaRepentanceMarriageWealthWitness
end Gnosis.Witnesses.Islam
