import Gnosis.Witnesses.Hindu.GitaDiscernmentVeilWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 8. -/

structure SupremeService where
  brahmaAsEternal : Bool := true
  karmaAsLifeGoingForth : Bool := true
  deathThoughtShapesDestination : Bool := true
  heartAlwaysFixedAndFight : Bool := true
  sensesShutAtDeath : Bool := true
  omMeditation : Bool := true
  noReturnAfterAttainingSupreme : Bool := true
  brahmaDayNightCycle : Bool := true
  unmanifestEnduresBeyondCreated : Bool := true
  wisdomOutranksRiteFruit : Bool := true
deriving Repr, DecidableEq

def supremeService : SupremeService := {}

theorem gita_supreme_service_witness :
    supremeService.brahmaAsEternal = true ∧
      supremeService.karmaAsLifeGoingForth = true ∧
      supremeService.deathThoughtShapesDestination = true ∧
      supremeService.heartAlwaysFixedAndFight = true ∧
      supremeService.noReturnAfterAttainingSupreme = true ∧
      supremeService.unmanifestEnduresBeyondCreated = true ∧
      supremeService.wisdomOutranksRiteFruit = true := by
  simp [supremeService]

end Gnosis.Witnesses.Hindu
