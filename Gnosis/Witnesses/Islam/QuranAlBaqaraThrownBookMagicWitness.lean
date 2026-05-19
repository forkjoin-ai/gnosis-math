import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraThrownBookMagicWitness

/-!
# Quran 2:101-103, Al-Baqara -- Thrown Book, Solomon, Harmful Knowledge

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1263-1280`.

This bounded witness tracks the Book-thrown-away and harmful-knowledge unit:

  * a confirming messenger comes from God;
  * some recipients of Scripture throw the Book of God behind them;
  * fabricated claims about Solomon are followed, while Solomon is cleared;
  * the evil ones teach witchcraft and what was revealed to Harut and Marut;
  * the two angels warn that they are a temptation and forbid disbelief;
  * the learned knowledge causes marital discord only by God's leave;
  * harmful, non-beneficial knowledge is chosen despite known Hereafter loss;
  * belief and mindfulness would have brought a better reward from God.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive ThrownBookMagicMoment
  | confirmingMessenger
  | bookThrownAway
  | solomonCleared
  | evilOnesTeach
  | angelsWarn
  | discordKnowledge
  | harmNotBenefit
  | hereafterShareLost
  | betterRewardAvailable
deriving DecidableEq, Repr

def thrownBookMagicMoments : List ThrownBookMagicMoment :=
  [ ThrownBookMagicMoment.confirmingMessenger
  , ThrownBookMagicMoment.bookThrownAway
  , ThrownBookMagicMoment.solomonCleared
  , ThrownBookMagicMoment.evilOnesTeach
  , ThrownBookMagicMoment.angelsWarn
  , ThrownBookMagicMoment.discordKnowledge
  , ThrownBookMagicMoment.harmNotBenefit
  , ThrownBookMagicMoment.hereafterShareLost
  , ThrownBookMagicMoment.betterRewardAvailable
  ]

structure ThrownBookPattern where
  messengerSentByGod : Bool
  messengerConfirmsScriptures : Bool
  scriptureRecipientsNamed : Bool
  bookOfGodThrownBehindShoulders : Bool
  noKnowledgePosture : Bool
deriving DecidableEq, Repr

def thrownBookPattern : ThrownBookPattern where
  messengerSentByGod := true
  messengerConfirmsScriptures := true
  scriptureRecipientsNamed := true
  bookOfGodThrownBehindShoulders := true
  noKnowledgePosture := true

structure SolomonMagicPattern where
  evilOnesFabricated : Bool
  kingdomSolomonNamed : Bool
  solomonNotDisbeliever : Bool
  evilOnesDisbelievers : Bool
  witchcraftTaught : Bool
  babylonRevelationNamed : Bool
  harutNamed : Bool
  marutNamed : Bool
  temptationWarning : Bool
  disbeliefForbidden : Bool
deriving DecidableEq, Repr

def solomonMagicPattern : SolomonMagicPattern where
  evilOnesFabricated := true
  kingdomSolomonNamed := true
  solomonNotDisbeliever := true
  evilOnesDisbelievers := true
  witchcraftTaught := true
  babylonRevelationNamed := true
  harutNamed := true
  marutNamed := true
  temptationWarning := true
  disbeliefForbidden := true

structure HarmRewardPattern where
  maritalDiscordCaused : Bool
  harmOnlyByGodLeave : Bool
  harmfulKnowledgeLearned : Bool
  nonbeneficialKnowledgeLearned : Bool
  hereafterShareLost : Bool
  soulsSoldEvilPrice : Bool
  beliefWouldHelp : Bool
  mindfulnessWouldHelp : Bool
  betterRewardFromGod : Bool
deriving DecidableEq, Repr

def harmRewardPattern : HarmRewardPattern where
  maritalDiscordCaused := true
  harmOnlyByGodLeave := true
  harmfulKnowledgeLearned := true
  nonbeneficialKnowledgeLearned := true
  hereafterShareLost := true
  soulsSoldEvilPrice := true
  beliefWouldHelp := true
  mindfulnessWouldHelp := true
  betterRewardFromGod := true

theorem quran_al_baqara_thrown_book_magic_witness :
    thrownBookMagicMoments.length = 9
    ∧ thrownBookMagicMoments.head? = some ThrownBookMagicMoment.confirmingMessenger
    ∧ thrownBookMagicMoments.getLast? = some ThrownBookMagicMoment.betterRewardAvailable
    ∧ thrownBookPattern.messengerSentByGod = true
    ∧ thrownBookPattern.messengerConfirmsScriptures = true
    ∧ thrownBookPattern.bookOfGodThrownBehindShoulders = true
    ∧ solomonMagicPattern.evilOnesFabricated = true
    ∧ solomonMagicPattern.solomonNotDisbeliever = true
    ∧ solomonMagicPattern.evilOnesDisbelievers = true
    ∧ solomonMagicPattern.witchcraftTaught = true
    ∧ solomonMagicPattern.harutNamed = true
    ∧ solomonMagicPattern.marutNamed = true
    ∧ solomonMagicPattern.temptationWarning = true
    ∧ solomonMagicPattern.disbeliefForbidden = true
    ∧ harmRewardPattern.maritalDiscordCaused = true
    ∧ harmRewardPattern.harmOnlyByGodLeave = true
    ∧ harmRewardPattern.harmfulKnowledgeLearned = true
    ∧ harmRewardPattern.nonbeneficialKnowledgeLearned = true
    ∧ harmRewardPattern.hereafterShareLost = true
    ∧ harmRewardPattern.soulsSoldEvilPrice = true
    ∧ harmRewardPattern.beliefWouldHelp = true
    ∧ harmRewardPattern.mindfulnessWouldHelp = true
    ∧ harmRewardPattern.betterRewardFromGod = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraThrownBookMagicWitness
end Gnosis.Witnesses.Islam
