import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 10. -/

structure PerfectionsCatalogue where
  distributedNaturesSpringFromSource : Bool := true
  wisdomLampDispelsIgnorance : Bool := true
  excellenceCataloguedAsPortions : Bool := true
  spiritSeatedInCreatureHeart : Bool := true
  firstLastCentre : Bool := true
  seedOfAllWhichSprings : Bool := true
  wondrousMajestyMightProceedFromSource : Bool := true
  portionsPointToSource : Bool := true
  separateLordAbides : Bool := true
deriving Repr, DecidableEq

def perfectionsCatalogue : PerfectionsCatalogue := {}

theorem gita_perfections_catalogue_witness :
    perfectionsCatalogue.distributedNaturesSpringFromSource = true ∧
      perfectionsCatalogue.wisdomLampDispelsIgnorance = true ∧
      perfectionsCatalogue.excellenceCataloguedAsPortions = true ∧
      perfectionsCatalogue.spiritSeatedInCreatureHeart = true ∧
      perfectionsCatalogue.seedOfAllWhichSprings = true ∧
      perfectionsCatalogue.wondrousMajestyMightProceedFromSource = true ∧
      perfectionsCatalogue.portionsPointToSource = true ∧
      perfectionsCatalogue.separateLordAbides = true := by
  simp [perfectionsCatalogue]

end Gnosis.Witnesses.Hindu
