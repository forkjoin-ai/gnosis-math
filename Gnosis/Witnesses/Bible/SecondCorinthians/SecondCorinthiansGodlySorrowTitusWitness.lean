import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansGodlySorrowTitusWitness

/-! # 2 Corinthians 7 -- Godly Sorrow and Titus Comfort
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93131-93188`. -/

structure GodlySorrowTitus where
  cleansePerfectingHoliness : Bool
  receiveUsWrongedCorruptedDefraudedNone : Bool
  comfortJoyInTribulation : Bool
  macedoniaFightingsFears : Bool
  godComfortedByTitus : Bool
  sorrowToRepentance : Bool
  godlySorrowSalvationWorldlySorrowDeath : Bool
  carefulnessClearingIndignationFearDesireZeal : Bool
  titusJoyRefreshed : Bool
  confidenceInAllThings : Bool
deriving DecidableEq, Repr

def godlySorrowTitus : GodlySorrowTitus where
  cleansePerfectingHoliness := true
  receiveUsWrongedCorruptedDefraudedNone := true
  comfortJoyInTribulation := true
  macedoniaFightingsFears := true
  godComfortedByTitus := true
  sorrowToRepentance := true
  godlySorrowSalvationWorldlySorrowDeath := true
  carefulnessClearingIndignationFearDesireZeal := true
  titusJoyRefreshed := true
  confidenceInAllThings := true

theorem second_corinthians_godly_sorrow_titus_witness :
    godlySorrowTitus.cleansePerfectingHoliness = true
    ∧ godlySorrowTitus.receiveUsWrongedCorruptedDefraudedNone = true
    ∧ godlySorrowTitus.comfortJoyInTribulation = true
    ∧ godlySorrowTitus.macedoniaFightingsFears = true
    ∧ godlySorrowTitus.godComfortedByTitus = true
    ∧ godlySorrowTitus.sorrowToRepentance = true
    ∧ godlySorrowTitus.godlySorrowSalvationWorldlySorrowDeath = true
    ∧ godlySorrowTitus.carefulnessClearingIndignationFearDesireZeal = true
    ∧ godlySorrowTitus.titusJoyRefreshed = true
    ∧ godlySorrowTitus.confidenceInAllThings = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansGodlySorrowTitusWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
