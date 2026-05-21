import Gnosis.Witnesses.Bible.Hebrews.HebrewsSonAngelsWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsDriftSufferingWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsHouseHardeningWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsRestWordWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsPriesthoodMaturityWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsFoundationAnchorWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsMelchisedecEndlessLifeWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsBetterCovenantWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsBloodConscienceWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsOnceForAllEnduranceWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsFaithLedgerWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsRaceDisciplineKingdomWitness
import Gnosis.Witnesses.Bible.Hebrews.HebrewsOutsideCampGraceWitness

namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsSourceQualityWitness

/-!
# Hebrews -- Opening Source Quality Spine

Book-level invariant, opened in chapters 1-13: Hebrews tests every mediator, rite,
and covenantal support against the Son's completed speech, completed purgation,
completed session, suffering solidarity, and Son-over-house rank. The source is
not merely comparative religion; it is a rank audit of what can actually bear
finality without losing the endangered hearer. The promised rest remains open
only where the heard word is mixed with faith, and priesthood is validated by
calling, compassion, suffered obedience, and trained discernment. Maturity moves
from foundation toward perfection under the oath-anchored promise. Melchisedec
then proves that priesthood rank can outrun Levitical descent by endless life.
The true tabernacle and better covenant move the rank audit from priesthood into
sanctuary and covenant architecture. The blood/conscience argument then exposes
why a figured sanctuary cannot be final even when its service is real. The
once-for-all offering converts final access into communal endurance. Faith then
appears as the ancestral ledger of action before visibility. The witness cloud
then becomes a race under discipline toward an unshaken kingdom.
Finally, stable grace sends the unshaken people outside the camp with sacrifices
of praise, sharing, and honest endurance.

Primary gap/counterproof: a created or delegated mediator can be glorious while
still failing the finality test. Hebrews grants angelic ministry and steadfast
angel-spoken speech, then refuses angels the Son's name, throne, permanence,
right-hand victory, world-to-come dominion, flesh-sharing descent, and death-
breaking priesthood. It also grants Moses real faithfulness as servant while
refusing servant/testimony status the builder/Son rank. It grants Sabbath and
Joshua real witness while refusing either as a premature closure of rest. It
also grants priestly office real honor while rejecting self-glorified office and
dull-hearing immaturity. It grants first principles real foundation status while
rejecting endless relaying and cheap renewal after apostasy. It grants Levi real
legal office while rejecting mortality and carnal commandment as final access.
It grants Mosaic pattern real authority while rejecting shadow-service finality.
It grants first-covenant ordinances real divine service while rejecting their
ability to perfect conscience or manifest the holiest way.
It grants the law's shadow real anticipatory shape while rejecting repeated
sacrifice as a holy-looking technology for preserving incompletion.
It grants visible possession practical force while rejecting it as the measure
of truth, promise, or report.
It grants present pain real grief while rejecting comfort as the proof of sonship
and shaking as the proof of loss.
It grants tabernacle service real history while rejecting camp belonging as the
measure of sanctification.

Unseen sat: the durable witness is not untouched height but faithful remainder
after descent. The heavens can be folded, ministries can be sent, speech can
arrive through many modes, and death can expose bondage; the Son remains by
entering the tested field and returning with succour. The house remains by
today-hearing rather than fossilized proximity to past signs. Exposure by the
living word becomes bearable because the high priest turns naked manifestation
into bold access to mercy. Strong meat names not elitism but exercised senses.
The anchor enters within the veil, so the harsh warning is bounded by immutable
counsel rather than panic. Abraham's tithe becomes an archaeological witness
that the later law already carries a higher priesthood upstream of itself.
Interiorized law is the sat hidden inside covenant change: not bare novelty, but
mind, heart, peoplehood, mercy, and remembered-no-more sin.
Christ's own blood is the transition from external purification to conscience
purging, and once-for-all appearance prevents finality from becoming repetition.
The new and living way is therefore not permission to become private; it is the
ground of assembled exhortation, holy warning, and patient faith.
The elders teach the contrarian rule: unseen evidence is not lesser evidence
when the object itself is not yet visible.
The sage rule of discipline is sharper: not every wound is abandonment, and not
everything that stands has the right to remain.
The closing rule is stranger still: the fulfilled altar is found by leaving the
respectable camp that thinks it owns holiness.

No `sorry`, no new `axiom`.
-/

structure HebrewsOpeningInvariant where
  finalSpeechIsSonShaped : Bool := true
  purgationPrecedesSession : Bool := true
  mediationMustPassFinalityTest : Bool := true
  sufferingSolidarityCompletesPriesthood : Bool := true
  sonOverHouseRanksServantWitness : Bool := true
  promisedRestRequiresFaithMixedHearing : Bool := true
  priesthoodRequiresCallingAndSuffering : Bool := true
  maturityMovesBeyondEndlessFoundation : Bool := true
  hopeAnchorsWithinTheVeil : Bool := true
  melchisedecRankChangesPriesthoodLaw : Bool := true
  betterCovenantInternalizesLaw : Bool := true
  ownBloodPurgesConscienceOnce : Bool := true
  oneOfferingGroundsBoldEndurance : Bool := true
  faithActsBeforeVisibility : Bool := true
  disciplineTrainsForUnshakenKingdom : Bool := true
  stableGraceGoesOutsideCamp : Bool := true
  remainderOutlastsFoldedCreation : Bool := true
deriving DecidableEq, Repr

def hebrewsOpeningInvariant : HebrewsOpeningInvariant := {}

def finalityRankInvariant (i : HebrewsOpeningInvariant) : Prop :=
  i.finalSpeechIsSonShaped = true ∧
  i.purgationPrecedesSession = true ∧
  i.mediationMustPassFinalityTest = true ∧
  i.sufferingSolidarityCompletesPriesthood = true ∧
  i.sonOverHouseRanksServantWitness = true ∧
  i.promisedRestRequiresFaithMixedHearing = true ∧
  i.priesthoodRequiresCallingAndSuffering = true ∧
  i.maturityMovesBeyondEndlessFoundation = true ∧
  i.hopeAnchorsWithinTheVeil = true ∧
  i.melchisedecRankChangesPriesthoodLaw = true ∧
  i.betterCovenantInternalizesLaw = true ∧
  i.ownBloodPurgesConscienceOnce = true ∧
  i.oneOfferingGroundsBoldEndurance = true ∧
  i.faithActsBeforeVisibility = true ∧
  i.disciplineTrainsForUnshakenKingdom = true ∧
  i.stableGraceGoesOutsideCamp = true ∧
  i.remainderOutlastsFoldedCreation = true

structure HebrewsOpeningCounterproof where
  messengerFireCannotEqualThrone : Bool := true
  sentMinistryCannotEqualInheritanceName : Bool := true
  createdHeavensCannotEqualUnchangedYears : Bool := true
  rightHandVictoryCannotBeDelegatedToAngels : Bool := true
  angelNatureCannotBreakFleshDeathBondage : Bool := true
  exodusSignsCannotReplaceTodayFaith : Bool := true
  pastRestMarkersCannotCloseRemainingRest : Bool := true
  dullHearingCannotCarryMelchisedecMeat : Bool := true
  tastedPowerCannotLicenseFruitlessApostasy : Bool := true
  mortalPriesthoodCannotSaveUttermost : Bool := true
  shadowServiceCannotCarryCovenantFinality : Bool := true
  firstTabernacleCannotManifestHoliestWay : Bool := true
  repeatedOfferingCannotBeFinalAppearance : Bool := true
  willfulContemptCannotClaimMoreSacrifice : Bool := true
  visiblePossessionCannotMeasurePromise : Bool := true
  comfortCannotProveSonship : Bool := true
  shakenThingsCannotClaimFinalKingdom : Bool := true
  meatCenteredReligionCannotEstablishHeart : Bool := true
  campBelongingCannotOwnHoliness : Bool := true
deriving DecidableEq, Repr

def hebrewsOpeningCounterproof : HebrewsOpeningCounterproof := {}

def angelicFinalityRejected (c : HebrewsOpeningCounterproof) : Prop :=
  c.messengerFireCannotEqualThrone = true ∧
  c.sentMinistryCannotEqualInheritanceName = true ∧
  c.createdHeavensCannotEqualUnchangedYears = true ∧
  c.rightHandVictoryCannotBeDelegatedToAngels = true ∧
  c.angelNatureCannotBreakFleshDeathBondage = true ∧
  c.exodusSignsCannotReplaceTodayFaith = true ∧
  c.pastRestMarkersCannotCloseRemainingRest = true ∧
  c.dullHearingCannotCarryMelchisedecMeat = true ∧
  c.tastedPowerCannotLicenseFruitlessApostasy = true ∧
  c.mortalPriesthoodCannotSaveUttermost = true ∧
  c.shadowServiceCannotCarryCovenantFinality = true ∧
  c.firstTabernacleCannotManifestHoliestWay = true ∧
  c.repeatedOfferingCannotBeFinalAppearance = true ∧
  c.willfulContemptCannotClaimMoreSacrifice = true ∧
  c.visiblePossessionCannotMeasurePromise = true ∧
  c.comfortCannotProveSonship = true ∧
  c.shakenThingsCannotClaimFinalKingdom = true ∧
  c.meatCenteredReligionCannotEstablishHeart = true ∧
  c.campBelongingCannotOwnHoliness = true

theorem hebrews_opening_quality_invariant :
    finalityRankInvariant hebrewsOpeningInvariant := by
  unfold finalityRankInvariant hebrewsOpeningInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_opening_quality_counterproof :
    angelicFinalityRejected hebrewsOpeningCounterproof := by
  unfold angelicFinalityRejected hebrewsOpeningCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_source_quality_opening_witness :
    finalityRankInvariant hebrewsOpeningInvariant ∧
    angelicFinalityRejected hebrewsOpeningCounterproof ∧
    HebrewsSonAngelsWitness.finalSpeechWitness
      HebrewsSonAngelsWitness.finalSpeechField ∧
    HebrewsSonAngelsWitness.angelMediationCounterproof
      HebrewsSonAngelsWitness.angelBoundary ∧
    HebrewsDriftSufferingWitness.driftWarningWitness
      HebrewsDriftSufferingWitness.driftWarning ∧
    HebrewsDriftSufferingWitness.descentWitness
      HebrewsDriftSufferingWitness.sufferingDescent ∧
    HebrewsDriftSufferingWitness.deathBondageBroken
      HebrewsDriftSufferingWitness.deathBondageCounterproof ∧
    HebrewsHouseHardeningWitness.houseRankWitness
      HebrewsHouseHardeningWitness.houseRank ∧
    HebrewsHouseHardeningWitness.todayWarningWitness
      HebrewsHouseHardeningWitness.todayWarning ∧
    HebrewsHouseHardeningWitness.wildernessUnbeliefRejected
      HebrewsHouseHardeningWitness.wildernessCounterproof ∧
    HebrewsRestWordWitness.remainingRestWitness
      HebrewsRestWordWitness.remainingRest ∧
    HebrewsRestWordWitness.prematureRestClosureRejected
      HebrewsRestWordWitness.restCounterproof ∧
    HebrewsRestWordWitness.exposureMercyWitness
      HebrewsRestWordWitness.wordAndPriestAccess ∧
    HebrewsPriesthoodMaturityWitness.calledPriesthoodWitness
      HebrewsPriesthoodMaturityWitness.calledPriesthood ∧
    HebrewsPriesthoodMaturityWitness.sufferingObedienceWitness
      HebrewsPriesthoodMaturityWitness.sufferingObedience ∧
    HebrewsPriesthoodMaturityWitness.dullHearingRejected
      HebrewsPriesthoodMaturityWitness.hearingMaturityCounterproof ∧
    HebrewsFoundationAnchorWitness.foundationAdvanceWitness
      HebrewsFoundationAnchorWitness.foundationAdvance ∧
    HebrewsFoundationAnchorWitness.cheapRenewalRejected
      HebrewsFoundationAnchorWitness.impossibleRenewalCounterproof ∧
    HebrewsFoundationAnchorWitness.oathAnchorWitness
      HebrewsFoundationAnchorWitness.oathAnchorConsolation ∧
    HebrewsMelchisedecEndlessLifeWitness.melchisedecRankWitness
      HebrewsMelchisedecEndlessLifeWitness.melchisedecRank ∧
    HebrewsMelchisedecEndlessLifeWitness.priesthoodLawChangeWitness
      HebrewsMelchisedecEndlessLifeWitness.priesthoodLawChange ∧
    HebrewsMelchisedecEndlessLifeWitness.mortalPriesthoodRejected
      HebrewsMelchisedecEndlessLifeWitness.mortalPriesthoodCounterproof ∧
    HebrewsBetterCovenantWitness.heavenlySanctuaryWitness
      HebrewsBetterCovenantWitness.heavenlySanctuary ∧
    HebrewsBetterCovenantWitness.betterCovenantWitness
      HebrewsBetterCovenantWitness.betterCovenant ∧
    HebrewsBetterCovenantWitness.shadowFinalityRejected
      HebrewsBetterCovenantWitness.internalizedCovenantCounterproof ∧
    HebrewsBloodConscienceWitness.sanctuaryFigureWitness
      HebrewsBloodConscienceWitness.worldlySanctuaryFigure ∧
    HebrewsBloodConscienceWitness.consciencePurificationWitness
      HebrewsBloodConscienceWitness.consciencePurification ∧
    HebrewsBloodConscienceWitness.repeatedFigureFinalityRejected
      HebrewsBloodConscienceWitness.testamentOnceCounterproof ∧
    HebrewsOnceForAllEnduranceWitness.repeatedSacrificeRejected
      HebrewsOnceForAllEnduranceWitness.shadowSacrificeCounterproof ∧
    HebrewsOnceForAllEnduranceWitness.onceForAllWitness
      HebrewsOnceForAllEnduranceWitness.onceForAllOffering ∧
    HebrewsOnceForAllEnduranceWitness.boldEntryCommunityWitness
      HebrewsOnceForAllEnduranceWitness.boldEntryCommunity ∧
    HebrewsOnceForAllEnduranceWitness.enduranceWarningWitness
      HebrewsOnceForAllEnduranceWitness.willfulSinEndurance ∧
    HebrewsFaithLedgerWitness.faithSubstanceWitness
      HebrewsFaithLedgerWitness.faithSubstance ∧
    HebrewsFaithLedgerWitness.pilgrimPromiseWitness
      HebrewsFaithLedgerWitness.pilgrimPromise ∧
    HebrewsFaithLedgerWitness.exodusRefusalWitness
      HebrewsFaithLedgerWitness.exodusRefusal ∧
    HebrewsFaithLedgerWitness.visiblePossessionFinalityRejected
      HebrewsFaithLedgerWitness.worldUnworthyCounterproof ∧
    HebrewsRaceDisciplineKingdomWitness.witnessRaceWitness
      HebrewsRaceDisciplineKingdomWitness.witnessRace ∧
    HebrewsRaceDisciplineKingdomWitness.disciplineSonshipWitness
      HebrewsRaceDisciplineKingdomWitness.disciplineSonship ∧
    HebrewsRaceDisciplineKingdomWitness.shortTermTradeRejected
      HebrewsRaceDisciplineKingdomWitness.bitterTradeCounterproof ∧
    HebrewsRaceDisciplineKingdomWitness.unshakenKingdomWitness
      HebrewsRaceDisciplineKingdomWitness.unshakenKingdom ∧
    HebrewsOutsideCampGraceWitness.graceSocialFormWitness
      HebrewsOutsideCampGraceWitness.graceSocialForm ∧
    HebrewsOutsideCampGraceWitness.stableGraceAltarWitness
      HebrewsOutsideCampGraceWitness.stableGraceAltar ∧
    HebrewsOutsideCampGraceWitness.remainingSacrificeWitness
      HebrewsOutsideCampGraceWitness.remainingSacrifice := by
  exact ⟨hebrews_opening_quality_invariant,
    hebrews_opening_quality_counterproof,
    HebrewsSonAngelsWitness.hebrews_final_speech,
    HebrewsSonAngelsWitness.hebrews_angel_boundary,
    HebrewsDriftSufferingWitness.hebrews_drift_warning,
    HebrewsDriftSufferingWitness.hebrews_suffering_descent,
    HebrewsDriftSufferingWitness.hebrews_death_bondage_broken,
    HebrewsHouseHardeningWitness.hebrews_house_rank,
    HebrewsHouseHardeningWitness.hebrews_today_warning,
    HebrewsHouseHardeningWitness.hebrews_wilderness_counterproof,
    HebrewsRestWordWitness.hebrews_remaining_rest,
    HebrewsRestWordWitness.hebrews_premature_rest_closure_rejected,
    HebrewsRestWordWitness.hebrews_exposure_mercy,
    HebrewsPriesthoodMaturityWitness.hebrews_called_priesthood,
    HebrewsPriesthoodMaturityWitness.hebrews_suffering_obedience,
    HebrewsPriesthoodMaturityWitness.hebrews_dull_hearing_rejected,
    HebrewsFoundationAnchorWitness.hebrews_foundation_advance,
    HebrewsFoundationAnchorWitness.hebrews_cheap_renewal_rejected,
    HebrewsFoundationAnchorWitness.hebrews_oath_anchor,
    HebrewsMelchisedecEndlessLifeWitness.hebrews_melchisedec_rank,
    HebrewsMelchisedecEndlessLifeWitness.hebrews_priesthood_law_change,
    HebrewsMelchisedecEndlessLifeWitness.hebrews_mortal_priesthood_rejected,
    HebrewsBetterCovenantWitness.hebrews_heavenly_sanctuary,
    HebrewsBetterCovenantWitness.hebrews_better_covenant,
    HebrewsBetterCovenantWitness.hebrews_shadow_finality_rejected,
    HebrewsBloodConscienceWitness.hebrews_sanctuary_figure,
    HebrewsBloodConscienceWitness.hebrews_conscience_purification,
    HebrewsBloodConscienceWitness.hebrews_repeated_figure_finality_rejected,
    HebrewsOnceForAllEnduranceWitness.hebrews_repeated_sacrifice_rejected,
    HebrewsOnceForAllEnduranceWitness.hebrews_once_for_all,
    HebrewsOnceForAllEnduranceWitness.hebrews_bold_entry_community,
    HebrewsOnceForAllEnduranceWitness.hebrews_endurance_warning,
    HebrewsFaithLedgerWitness.hebrews_faith_substance,
    HebrewsFaithLedgerWitness.hebrews_pilgrim_promise,
    HebrewsFaithLedgerWitness.hebrews_exodus_refusal,
    HebrewsFaithLedgerWitness.hebrews_visible_possession_finality_rejected,
    HebrewsRaceDisciplineKingdomWitness.hebrews_witness_race,
    HebrewsRaceDisciplineKingdomWitness.hebrews_discipline_sonship,
    HebrewsRaceDisciplineKingdomWitness.hebrews_short_term_trade_rejected,
    HebrewsRaceDisciplineKingdomWitness.hebrews_unshaken_kingdom,
    HebrewsOutsideCampGraceWitness.hebrews_grace_social_form,
    HebrewsOutsideCampGraceWitness.hebrews_stable_grace_altar,
    HebrewsOutsideCampGraceWitness.hebrews_remaining_sacrifice⟩

end HebrewsSourceQualityWitness
end Gnosis.Witnesses.Bible.Hebrews
