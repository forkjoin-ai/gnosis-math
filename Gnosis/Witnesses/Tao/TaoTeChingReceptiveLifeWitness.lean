import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Tao

/-!
# Tao Te Ching Receptive Life Witness

Witness ledger for `docs/ebooks/source-texts/tao-te-ching-legge.txt`,
chapters 49-51.

These chapters name a runtime without private rigidity. The sage has no fixed
mind, returns good and sincerity even to their absence, gives death no place to
enter, and models Tao's mysterious operation: produce, nourish, mature, and
maintain without possession, boasting, or control.
-/

/-- Chapter 49: witness mind is receptive rather than privately fixed. -/
structure ReceptiveWitnessMind where
  noInvariablePrivateMind : Bool := true
  peoplesMindAsOwn : Bool := true
  goodReturnedToNotGood : Bool := true
  sincereReturnedToNotSincere : Bool := true
  treatsAllAsChildren : Bool := true
deriving Repr, DecidableEq

/-- Chapter 50: non-grasping life gives death no attack surface. -/
structure NoPlaceOfDeath where
  excessiveLifeSeekingMovesToDeath : Bool := true
  skilledLifeManagerTravelsUnharmed : Bool := true
  hornFindsNoPlace : Bool := true
  clawFindsNoPlace : Bool := true
  weaponFindsNoPlace : Bool := true
deriving Repr, DecidableEq

/-- Chapter 51: mysterious operation produces without owning or controlling. -/
structure MysteriousOperation where
  taoProducesAllThings : Bool := true
  operationNourishesAllThings : Bool := true
  completionFitsCircumstance : Bool := true
  noPossessionClaim : Bool := true
  noVauntingAbility : Bool := true
  noControlOverMaturity : Bool := true
deriving Repr, DecidableEq

def receptiveWitnessMind : ReceptiveWitnessMind := {}

def noPlaceOfDeath : NoPlaceOfDeath := {}

def mysteriousOperation : MysteriousOperation := {}

theorem tao_receptive_witness_mind :
    receptiveWitnessMind.noInvariablePrivateMind = true ∧
      receptiveWitnessMind.peoplesMindAsOwn = true ∧
      receptiveWitnessMind.goodReturnedToNotGood = true ∧
      receptiveWitnessMind.sincereReturnedToNotSincere = true ∧
      receptiveWitnessMind.treatsAllAsChildren = true := by
  simp [receptiveWitnessMind]

theorem tao_no_place_of_death :
    noPlaceOfDeath.excessiveLifeSeekingMovesToDeath = true ∧
      noPlaceOfDeath.skilledLifeManagerTravelsUnharmed = true ∧
      noPlaceOfDeath.hornFindsNoPlace = true ∧
      noPlaceOfDeath.clawFindsNoPlace = true ∧
      noPlaceOfDeath.weaponFindsNoPlace = true := by
  simp [noPlaceOfDeath]

theorem tao_mysterious_operation :
    mysteriousOperation.taoProducesAllThings = true ∧
      mysteriousOperation.operationNourishesAllThings = true ∧
      mysteriousOperation.completionFitsCircumstance = true ∧
      mysteriousOperation.noPossessionClaim = true ∧
      mysteriousOperation.noVauntingAbility = true ∧
      mysteriousOperation.noControlOverMaturity = true := by
  simp [mysteriousOperation]

/--
Chapters 49-51 witness the runtime as receptive life rather than possessive
control: the sage accepts the people's mind, leaves death no local hook, and
produces without ownership.
-/
theorem tao_te_ching_receptive_life_witness :
    receptiveWitnessMind.noInvariablePrivateMind = true ∧
      receptiveWitnessMind.goodReturnedToNotGood = true ∧
      noPlaceOfDeath.weaponFindsNoPlace = true ∧
      mysteriousOperation.taoProducesAllThings = true ∧
      mysteriousOperation.noPossessionClaim = true ∧
      mysteriousOperation.noControlOverMaturity = true := by
  simp [receptiveWitnessMind, noPlaceOfDeath, mysteriousOperation]

end Gnosis.Witnesses.Tao
