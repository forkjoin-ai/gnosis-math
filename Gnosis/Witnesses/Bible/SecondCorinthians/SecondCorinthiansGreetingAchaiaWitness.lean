import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansGreetingAchaiaWitness

/-! # 2 Corinthians 1:1-2 -- Greeting to Corinth and Achaia
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92810-92813`. -/

structure GreetingAchaia where
  paulApostleByWillOfGod : Bool
  timothyBrotherNamed : Bool
  churchOfGodAtCorinth : Bool
  saintsInAllAchaia : Bool
  graceAndPeaceFromFatherAndChrist : Bool
deriving DecidableEq, Repr

def greetingAchaia : GreetingAchaia where
  paulApostleByWillOfGod := true
  timothyBrotherNamed := true
  churchOfGodAtCorinth := true
  saintsInAllAchaia := true
  graceAndPeaceFromFatherAndChrist := true

theorem second_corinthians_greeting_achaia_witness :
    greetingAchaia.paulApostleByWillOfGod = true
    ∧ greetingAchaia.timothyBrotherNamed = true
    ∧ greetingAchaia.churchOfGodAtCorinth = true
    ∧ greetingAchaia.saintsInAllAchaia = true
    ∧ greetingAchaia.graceAndPeaceFromFatherAndChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansGreetingAchaiaWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
