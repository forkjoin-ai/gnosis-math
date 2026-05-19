import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyApocalypseNewJerusalemWitness

/-!
# Science and Health, Chapter XVI -- New Jerusalem and Love Shepherd

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:23280-23520`.

Bounded section: 572:18-578:18. This Apocalypse closing unit interprets the new
heaven and earth, New Jerusalem, city foursquare, no temple, Father-Mother
unity, four cardinal points, and Psalm XXIII through divine Love.
-/

inductive ApocalypseNewJerusalemMoment where
  | newHeavenNewEarthNoSea
  | johnVisionNotOptical
  | matterSpiritStatesConsciousness
  | godWithMenHarmony
  | spiritualSensePresentPossibility
  | vialMessageConsoles
  | miseryCompensatedByLove
  | afflictionBecomesAngel
  | lambWifeLoveIdea
  | plaguesDestroyedByRevelation
  | cityFoursquareScience
  | fourSidesWordChristChristianityScience
  | gatesNoNight
  | royalGatesCardinalStars
  | newJerusalemSeenWhileMortal
  | noTempleNoBody
  | kingdomWithinReach
  | lordSenseTransfigured
  | fatherMotherUnity
  | cityNoBoundary
  | loveLightMindInterpreter
  | nothingFalseEnters
  | revelationAcmeScience
  | psalmLoveShepherd
  | loveRestoresSpiritualSense
  | loveComfortsThroughDeathShadow
  | loveDwellingForever
deriving DecidableEq, Repr

def apocalypseNewJerusalemTrace : List ApocalypseNewJerusalemMoment :=
  [ ApocalypseNewJerusalemMoment.newHeavenNewEarthNoSea
  , ApocalypseNewJerusalemMoment.johnVisionNotOptical
  , ApocalypseNewJerusalemMoment.matterSpiritStatesConsciousness
  , ApocalypseNewJerusalemMoment.godWithMenHarmony
  , ApocalypseNewJerusalemMoment.spiritualSensePresentPossibility
  , ApocalypseNewJerusalemMoment.vialMessageConsoles
  , ApocalypseNewJerusalemMoment.miseryCompensatedByLove
  , ApocalypseNewJerusalemMoment.afflictionBecomesAngel
  , ApocalypseNewJerusalemMoment.lambWifeLoveIdea
  , ApocalypseNewJerusalemMoment.plaguesDestroyedByRevelation
  , ApocalypseNewJerusalemMoment.cityFoursquareScience
  , ApocalypseNewJerusalemMoment.fourSidesWordChristChristianityScience
  , ApocalypseNewJerusalemMoment.gatesNoNight
  , ApocalypseNewJerusalemMoment.royalGatesCardinalStars
  , ApocalypseNewJerusalemMoment.newJerusalemSeenWhileMortal
  , ApocalypseNewJerusalemMoment.noTempleNoBody
  , ApocalypseNewJerusalemMoment.kingdomWithinReach
  , ApocalypseNewJerusalemMoment.lordSenseTransfigured
  , ApocalypseNewJerusalemMoment.fatherMotherUnity
  , ApocalypseNewJerusalemMoment.cityNoBoundary
  , ApocalypseNewJerusalemMoment.loveLightMindInterpreter
  , ApocalypseNewJerusalemMoment.nothingFalseEnters
  , ApocalypseNewJerusalemMoment.revelationAcmeScience
  , ApocalypseNewJerusalemMoment.psalmLoveShepherd
  , ApocalypseNewJerusalemMoment.loveRestoresSpiritualSense
  , ApocalypseNewJerusalemMoment.loveComfortsThroughDeathShadow
  , ApocalypseNewJerusalemMoment.loveDwellingForever
  ]

structure ApocalypseNewJerusalem where
  newHeavenPresentPossibility : Bool
  cityFoursquareScience : Bool
  noTempleIncorporealMan : Bool
  fatherMotherUnity : Bool
  loveLight : Bool
  psalmReadThroughLove : Bool
deriving DecidableEq, Repr

def apocalypseNewJerusalem : ApocalypseNewJerusalem where
  newHeavenPresentPossibility := true
  cityFoursquareScience := true
  noTempleIncorporealMan := true
  fatherMotherUnity := true
  loveLight := true
  psalmReadThroughLove := true

theorem eddy_apocalypse_new_jerusalem_witness :
    apocalypseNewJerusalemTrace.length = 27
    ∧ apocalypseNewJerusalemTrace.head? =
      some ApocalypseNewJerusalemMoment.newHeavenNewEarthNoSea
    ∧ apocalypseNewJerusalemTrace.getLast? =
      some ApocalypseNewJerusalemMoment.loveDwellingForever
    ∧ apocalypseNewJerusalem.newHeavenPresentPossibility = true
    ∧ apocalypseNewJerusalem.cityFoursquareScience = true
    ∧ apocalypseNewJerusalem.noTempleIncorporealMan = true
    ∧ apocalypseNewJerusalem.fatherMotherUnity = true
    ∧ apocalypseNewJerusalem.loveLight = true
    ∧ apocalypseNewJerusalem.psalmReadThroughLove = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyApocalypseNewJerusalemWitness
end Gnosis.Witnesses.Eddy
