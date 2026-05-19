import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPlatformManCommandmentWitness

/-!
# Science and Health, Chapter X -- Platform XXII-XXXII and Commandment Closure

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:13980-14174`.

Bounded section: 336:1-340:27. This closes "Science of Being": immortal man
as God's reflected idea, God/man inseparable but not identical, Adam as
obstruction, pardon as destruction of sin, evil not God-produced, and the
First Commandment as the basis of the Science of being.
-/

inductive PlatformManCommandmentMoment where
  | intelligenceNeverPassesIntoMatter
  | immortalManImageIdea
  | infiniteMindReflectedNotContained
  | godIndivisibleNoPortion
  | godManInseparableNotSame
  | manReflectsPerfectGod
  | purityPathToPerfection
  | visibleUniverseCounterfeit
  | truthDemonstratedByHealing
  | materialPremisesEndInMortality
  | adamDustObstruction
  | christJesusIdealMan
  | pardonDestroysSin
  | evilNotProducedByGod
  | sinnerMustForsakeUnreal
  | materialTheoriesYieldToSpirit
  | onlyMindBasisHealth
  | errorConqueredByDenyingVerity
  | loveGodKeepCommandments
  | firstCommandmentDemonstratesScience
  | oneMindUnifiesMenAndNations
  | commandmentAnnulsIdolatryCurse
deriving DecidableEq, Repr

def platformManCommandmentTrace : List PlatformManCommandmentMoment :=
  [ PlatformManCommandmentMoment.intelligenceNeverPassesIntoMatter
  , PlatformManCommandmentMoment.immortalManImageIdea
  , PlatformManCommandmentMoment.infiniteMindReflectedNotContained
  , PlatformManCommandmentMoment.godIndivisibleNoPortion
  , PlatformManCommandmentMoment.godManInseparableNotSame
  , PlatformManCommandmentMoment.manReflectsPerfectGod
  , PlatformManCommandmentMoment.purityPathToPerfection
  , PlatformManCommandmentMoment.visibleUniverseCounterfeit
  , PlatformManCommandmentMoment.truthDemonstratedByHealing
  , PlatformManCommandmentMoment.materialPremisesEndInMortality
  , PlatformManCommandmentMoment.adamDustObstruction
  , PlatformManCommandmentMoment.christJesusIdealMan
  , PlatformManCommandmentMoment.pardonDestroysSin
  , PlatformManCommandmentMoment.evilNotProducedByGod
  , PlatformManCommandmentMoment.sinnerMustForsakeUnreal
  , PlatformManCommandmentMoment.materialTheoriesYieldToSpirit
  , PlatformManCommandmentMoment.onlyMindBasisHealth
  , PlatformManCommandmentMoment.errorConqueredByDenyingVerity
  , PlatformManCommandmentMoment.loveGodKeepCommandments
  , PlatformManCommandmentMoment.firstCommandmentDemonstratesScience
  , PlatformManCommandmentMoment.oneMindUnifiesMenAndNations
  , PlatformManCommandmentMoment.commandmentAnnulsIdolatryCurse
  ]

structure PlatformManCommandment where
  mindNeverEntersFinite : Bool
  manReflectsGod : Bool
  godManInseparableNotIdentical : Bool
  adamObstruction : Bool
  pardonDestroysSin : Bool
  evilNotGodProduct : Bool
  onlyMindBasisHealth : Bool
  firstCommandmentBasis : Bool
  oneMindUnifies : Bool
  idolatryCurseAnnulled : Bool
deriving DecidableEq, Repr

def platformManCommandment : PlatformManCommandment where
  mindNeverEntersFinite := true
  manReflectsGod := true
  godManInseparableNotIdentical := true
  adamObstruction := true
  pardonDestroysSin := true
  evilNotGodProduct := true
  onlyMindBasisHealth := true
  firstCommandmentBasis := true
  oneMindUnifies := true
  idolatryCurseAnnulled := true

theorem eddy_platform_man_commandment_witness :
    platformManCommandmentTrace.length = 22
    ∧ platformManCommandmentTrace.head? =
      some PlatformManCommandmentMoment.intelligenceNeverPassesIntoMatter
    ∧ platformManCommandmentTrace.getLast? =
      some PlatformManCommandmentMoment.commandmentAnnulsIdolatryCurse
    ∧ platformManCommandment.mindNeverEntersFinite = true
    ∧ platformManCommandment.manReflectsGod = true
    ∧ platformManCommandment.godManInseparableNotIdentical = true
    ∧ platformManCommandment.adamObstruction = true
    ∧ platformManCommandment.pardonDestroysSin = true
    ∧ platformManCommandment.evilNotGodProduct = true
    ∧ platformManCommandment.onlyMindBasisHealth = true
    ∧ platformManCommandment.firstCommandmentBasis = true
    ∧ platformManCommandment.oneMindUnifies = true
    ∧ platformManCommandment.idolatryCurseAnnulled = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPlatformManCommandmentWitness
end Gnosis.Witnesses.Eddy
