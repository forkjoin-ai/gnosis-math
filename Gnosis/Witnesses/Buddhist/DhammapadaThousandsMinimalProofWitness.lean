import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Thousands Minimal Proof Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 8, "The Thousands".

Quantity loses to meaningful effect: one useful word, one moment of reverence,
or one day of seeing can outrank thousands of words, sacrifices, battles, or
years. Self-conquest is the non-transferable victory.
-/

structure OneWordBeatsThousand where
  oneSensibleWordQuiets : Bool := true
  oneGathaWordQuiets : Bool := true
  oneLawWordQuiets : Bool := true
  thousandSenselessWordsInferior : Bool := true
deriving Repr, DecidableEq

structure SelfConquestVictory where
  selfConquestGreaterThanBattle : Bool := true
  ownSelfConqueredBetterThanOthers : Bool := true
  godsCannotDefeatRestrainedVictory : Bool := true
  restraintStabilizesVictory : Bool := true
deriving Repr, DecidableEq

structure OneDaySeeing where
  homageOutranksHundredYearSacrifice : Bool := true
  reverenceOutranksOblation : Bool := true
  oneDayVirtuousBetterThanHundredVicious : Bool := true
  oneDayWiseBetterThanHundredIgnorant : Bool := true
  oneDaySeesBeginningEnd : Bool := true
  oneDaySeesImmortalPlace : Bool := true
  oneDaySeesHighestLaw : Bool := true
deriving Repr, DecidableEq

def oneWordBeatsThousand : OneWordBeatsThousand := {}
def selfConquestVictory : SelfConquestVictory := {}
def oneDaySeeing : OneDaySeeing := {}

theorem dhammapada_one_word_beats_thousand :
    oneWordBeatsThousand.oneSensibleWordQuiets = true ∧
      oneWordBeatsThousand.oneGathaWordQuiets = true ∧
      oneWordBeatsThousand.oneLawWordQuiets = true ∧
      oneWordBeatsThousand.thousandSenselessWordsInferior = true := by
  simp [oneWordBeatsThousand]

theorem dhammapada_self_conquest_victory :
    selfConquestVictory.selfConquestGreaterThanBattle = true ∧
      selfConquestVictory.ownSelfConqueredBetterThanOthers = true ∧
      selfConquestVictory.godsCannotDefeatRestrainedVictory = true ∧
      selfConquestVictory.restraintStabilizesVictory = true := by
  simp [selfConquestVictory]

theorem dhammapada_one_day_seeing :
    oneDaySeeing.homageOutranksHundredYearSacrifice = true ∧
      oneDaySeeing.reverenceOutranksOblation = true ∧
      oneDaySeeing.oneDayVirtuousBetterThanHundredVicious = true ∧
      oneDaySeeing.oneDayWiseBetterThanHundredIgnorant = true ∧
      oneDaySeeing.oneDaySeesBeginningEnd = true ∧
      oneDaySeeing.oneDaySeesImmortalPlace = true ∧
      oneDaySeeing.oneDaySeesHighestLaw = true := by
  simp [oneDaySeeing]

theorem dhammapada_thousands_minimal_proof_witness :
    oneWordBeatsThousand.oneLawWordQuiets = true ∧
      oneWordBeatsThousand.thousandSenselessWordsInferior = true ∧
      selfConquestVictory.selfConquestGreaterThanBattle = true ∧
      selfConquestVictory.restraintStabilizesVictory = true ∧
      oneDaySeeing.oneDaySeesBeginningEnd = true ∧
      oneDaySeeing.oneDaySeesHighestLaw = true := by
  simp [oneWordBeatsThousand, selfConquestVictory, oneDaySeeing]

end Gnosis.Witnesses.Buddhist
