import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansAbrahamHopeStrongFaithWitness

/-!
# Romans 4:18-22 (KJV) -- Abraham, Hope, and Strong Faith

This unit gives one bounded strong-faith topology:

  * Abraham against hope believed in hope;
  * he was not weak in faith despite his own body and Sarah's womb;
  * he did not stagger through unbelief;
  * he was strong in faith, gave glory to God, and was fully persuaded;
  * therefore it was imputed to him for righteousness.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 4:18-22 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_4_18_22_quote : String :=
  "4:18 Who against hope believed in hope, that he might become the " ++
  "father of many nations, according to that which was spoken, So shall " ++
  "thy seed be. 4:19 And being not weak in faith, he considered not his " ++
  "own body now dead, when he was about an hundred years old, neither " ++
  "yet the deadness of Sarah's womb: 4:20 He staggered not at the " ++
  "promise of God through unbelief; but was strong in faith, giving " ++
  "glory to God; 4:21 And being fully persuaded that, what he had " ++
  "promised, he was able also to perform. 4:22 And therefore it was " ++
  "imputed to him for righteousness."

/-- The hope and seed pattern in Romans 4:18. -/
structure HopeSeedPattern where
  againstHopeBelievedInHope : Bool
  becomeFatherOfManyNations : Bool
  soShallThySeedBe : Bool
deriving DecidableEq, Repr

/-- Abraham believes in hope according to the seed promise. -/
def hopeSeedPattern : HopeSeedPattern where
  againstHopeBelievedInHope := true
  becomeFatherOfManyNations := true
  soShallThySeedBe := true

/-- The strong-faith pattern in Romans 4:19-22. -/
structure StrongFaithPattern where
  notWeakInFaith : Bool
  consideredNotDeadBodyAndSarahWomb : Bool
  staggeredNotThroughUnbelief : Bool
  strongInFaithGivingGlory : Bool
  fullyPersuadedGodAbleToPerform : Bool
  imputedForRighteousness : Bool
deriving DecidableEq, Repr

/-- Abraham's strong faith concludes in imputed righteousness. -/
def strongFaithPattern : StrongFaithPattern where
  notWeakInFaith := true
  consideredNotDeadBodyAndSarahWomb := true
  staggeredNotThroughUnbelief := true
  strongInFaithGivingGlory := true
  fullyPersuadedGodAbleToPerform := true
  imputedForRighteousness := true

/-- The bounded Romans 4:18-22 witness. -/
theorem romans_abraham_hope_strong_faith_witness :
    hopeSeedPattern.againstHopeBelievedInHope = true
    ∧ hopeSeedPattern.becomeFatherOfManyNations = true
    ∧ hopeSeedPattern.soShallThySeedBe = true
    ∧ strongFaithPattern.notWeakInFaith = true
    ∧ strongFaithPattern.consideredNotDeadBodyAndSarahWomb = true
    ∧ strongFaithPattern.staggeredNotThroughUnbelief = true
    ∧ strongFaithPattern.strongInFaithGivingGlory = true
    ∧ strongFaithPattern.fullyPersuadedGodAbleToPerform = true
    ∧ strongFaithPattern.imputedForRighteousness = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansAbrahamHopeStrongFaithWitness
end Gnosis.Witnesses.Bible.Romans
