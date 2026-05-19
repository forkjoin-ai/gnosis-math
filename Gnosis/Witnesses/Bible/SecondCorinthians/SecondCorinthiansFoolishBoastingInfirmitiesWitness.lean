import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansFoolishBoastingInfirmitiesWitness

/-! # 2 Corinthians 11 -- Foolish Boasting and Infirmities
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93356-93453`. -/

structure FoolishBoastingInfirmities where
  godlyJealousyChasteVirginChrist : Bool
  serpentCorruptionFromSimplicity : Bool
  anotherJesusSpiritGospelWarning : Bool
  freeGospelNotBurdensome : Bool
  falseApostlesDeceitfulWorkers : Bool
  satanAngelLightMinistersRighteousness : Bool
  foolsGloryAfterFlesh : Bool
  hebrewIsraeliteAbrahamSeed : Bool
  laboursStripesPrisonsDeathsPerils : Bool
  careAllChurchesGloryInInfirmities : Bool
  damascusBasketEscape : Bool
deriving DecidableEq, Repr

def foolishBoastingInfirmities : FoolishBoastingInfirmities where
  godlyJealousyChasteVirginChrist := true
  serpentCorruptionFromSimplicity := true
  anotherJesusSpiritGospelWarning := true
  freeGospelNotBurdensome := true
  falseApostlesDeceitfulWorkers := true
  satanAngelLightMinistersRighteousness := true
  foolsGloryAfterFlesh := true
  hebrewIsraeliteAbrahamSeed := true
  laboursStripesPrisonsDeathsPerils := true
  careAllChurchesGloryInInfirmities := true
  damascusBasketEscape := true

theorem second_corinthians_foolish_boasting_infirmities_witness :
    foolishBoastingInfirmities.godlyJealousyChasteVirginChrist = true
    ∧ foolishBoastingInfirmities.serpentCorruptionFromSimplicity = true
    ∧ foolishBoastingInfirmities.anotherJesusSpiritGospelWarning = true
    ∧ foolishBoastingInfirmities.freeGospelNotBurdensome = true
    ∧ foolishBoastingInfirmities.falseApostlesDeceitfulWorkers = true
    ∧ foolishBoastingInfirmities.satanAngelLightMinistersRighteousness = true
    ∧ foolishBoastingInfirmities.foolsGloryAfterFlesh = true
    ∧ foolishBoastingInfirmities.hebrewIsraeliteAbrahamSeed = true
    ∧ foolishBoastingInfirmities.laboursStripesPrisonsDeathsPerils = true
    ∧ foolishBoastingInfirmities.careAllChurchesGloryInInfirmities = true
    ∧ foolishBoastingInfirmities.damascusBasketEscape = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansFoolishBoastingInfirmitiesWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
