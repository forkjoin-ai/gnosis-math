import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansStewardsApostlesPowerWitness

/-! # 1 Corinthians 4 -- Stewards, Apostles, and Power
Source text: `docs/ebooks/source-texts/bible-kjv.txt:91779-91841`. -/

structure StewardsApostlesPower where
  stewardsOfMysteries : Bool
  judgedByLordNotBeforeTime : Bool
  nothingReceivedAsIfNotReceived : Bool
  apostlesSetForthLast : Bool
  fatherInChristByGospel : Bool
  timotheusSentForRemembrance : Bool
  kingdomNotWordButPower : Bool
  rodOrLoveMeekness : Bool
deriving DecidableEq, Repr

def stewardsApostlesPower : StewardsApostlesPower where
  stewardsOfMysteries := true
  judgedByLordNotBeforeTime := true
  nothingReceivedAsIfNotReceived := true
  apostlesSetForthLast := true
  fatherInChristByGospel := true
  timotheusSentForRemembrance := true
  kingdomNotWordButPower := true
  rodOrLoveMeekness := true

theorem first_corinthians_stewards_apostles_power_witness :
    stewardsApostlesPower.stewardsOfMysteries = true
    ∧ stewardsApostlesPower.judgedByLordNotBeforeTime = true
    ∧ stewardsApostlesPower.nothingReceivedAsIfNotReceived = true
    ∧ stewardsApostlesPower.apostlesSetForthLast = true
    ∧ stewardsApostlesPower.fatherInChristByGospel = true
    ∧ stewardsApostlesPower.timotheusSentForRemembrance = true
    ∧ stewardsApostlesPower.kingdomNotWordButPower = true
    ∧ stewardsApostlesPower.rodOrLoveMeekness = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansStewardsApostlesPowerWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
