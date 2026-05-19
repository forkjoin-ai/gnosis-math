import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranBattleUsuryWitness

/-!
# Quran 3:121-148, Al Imran -- Battle Positions, Angels, Usury, and Steadfastness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2502-2571`.

This bounded witness tracks Quran 3:121-148:

  * the Prophet leaves at dawn to assign battle positions;
  * two groups almost lose heart, while God is protector;
  * Badr help is remembered when believers were weak;
  * angelic reinforcement gives hope and settles hearts, while help comes only from God;
  * the Prophet does not decide whether God relents toward or punishes opponents;
  * believers are warned against doubled usury and commanded to be mindful;
  * mercy is sought through obedience to God and the Prophet;
  * forgiveness and a Garden are promised to those who give, restrain anger, pardon,
    remember God after wrongdoing, seek forgiveness, and do not persist knowingly;
  * earlier ways are presented as a lesson from travel and observation;
  * alternating days distinguish believers, martyrs, and cleansing from destruction;
  * Garden is not entered without struggle and steadfastness being known;
  * Muhammad is only a messenger, so death or killing must not cause reversal;
  * death is by God's permission, and reward may be worldly or otherworldly;
  * prophets and godly people did not weaken, lose heart, or surrender.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive BattleUsuryMoment
  | battlePositions
  | twoGroupsProtected
  | badrHelp
  | angelsHeartsRest
  | prophetDecisionBoundary
  | usuryWarning
  | mercyObedience
  | righteousTraits
  | earlierWays
  | alternatingDays
  | struggleSteadfastness
  | messengerMortality
  | deathByPermission
  | godlySteadfastness
deriving DecidableEq, Repr

def battleUsuryMoments : List BattleUsuryMoment :=
  [ BattleUsuryMoment.battlePositions
  , BattleUsuryMoment.twoGroupsProtected
  , BattleUsuryMoment.badrHelp
  , BattleUsuryMoment.angelsHeartsRest
  , BattleUsuryMoment.prophetDecisionBoundary
  , BattleUsuryMoment.usuryWarning
  , BattleUsuryMoment.mercyObedience
  , BattleUsuryMoment.righteousTraits
  , BattleUsuryMoment.earlierWays
  , BattleUsuryMoment.alternatingDays
  , BattleUsuryMoment.struggleSteadfastness
  , BattleUsuryMoment.messengerMortality
  , BattleUsuryMoment.deathByPermission
  , BattleUsuryMoment.godlySteadfastness
  ]

structure BattleUsuryPattern where
  battlePositionsAssigned : Bool
  godProtectorNamed : Bool
  badrWeaknessRemembered : Bool
  angelsReinforceHope : Bool
  helpOnlyFromGod : Bool
  prophetDecisionBoundary : Bool
  doubledUsuryForbidden : Bool
  obedienceMercyLink : Bool
  angerRestrainedAndPardon : Bool
  forgivenessAfterWrongdoing : Bool
  earlierWaysLesson : Bool
  alternatingDaysNamed : Bool
  struggleSteadfastnessNamed : Bool
  messengerMortalityNamed : Bool
  deathByPermission : Bool
  prophetsDidNotSurrender : Bool
deriving DecidableEq, Repr

def battleUsuryPattern : BattleUsuryPattern where
  battlePositionsAssigned := true
  godProtectorNamed := true
  badrWeaknessRemembered := true
  angelsReinforceHope := true
  helpOnlyFromGod := true
  prophetDecisionBoundary := true
  doubledUsuryForbidden := true
  obedienceMercyLink := true
  angerRestrainedAndPardon := true
  forgivenessAfterWrongdoing := true
  earlierWaysLesson := true
  alternatingDaysNamed := true
  struggleSteadfastnessNamed := true
  messengerMortalityNamed := true
  deathByPermission := true
  prophetsDidNotSurrender := true

theorem quran_al_imran_battle_usury_witness :
    battleUsuryMoments.length = 14
    ∧ battleUsuryMoments.head? = some BattleUsuryMoment.battlePositions
    ∧ battleUsuryMoments.getLast? = some BattleUsuryMoment.godlySteadfastness
    ∧ battleUsuryPattern.battlePositionsAssigned = true
    ∧ battleUsuryPattern.godProtectorNamed = true
    ∧ battleUsuryPattern.badrWeaknessRemembered = true
    ∧ battleUsuryPattern.angelsReinforceHope = true
    ∧ battleUsuryPattern.helpOnlyFromGod = true
    ∧ battleUsuryPattern.prophetDecisionBoundary = true
    ∧ battleUsuryPattern.doubledUsuryForbidden = true
    ∧ battleUsuryPattern.obedienceMercyLink = true
    ∧ battleUsuryPattern.angerRestrainedAndPardon = true
    ∧ battleUsuryPattern.forgivenessAfterWrongdoing = true
    ∧ battleUsuryPattern.earlierWaysLesson = true
    ∧ battleUsuryPattern.alternatingDaysNamed = true
    ∧ battleUsuryPattern.struggleSteadfastnessNamed = true
    ∧ battleUsuryPattern.messengerMortalityNamed = true
    ∧ battleUsuryPattern.deathByPermission = true
    ∧ battleUsuryPattern.prophetsDidNotSurrender = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranBattleUsuryWitness
end Gnosis.Witnesses.Islam
