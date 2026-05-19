import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansBoastingExcludedFaithWitness

/-!
# Romans 3:27-28 (KJV) -- Boasting Excluded by Faith

This unit gives one bounded boasting/faith topology:

  * boasting is excluded;
  * not by the law of works, but by the law of faith;
  * a man is justified by faith without deeds of the law.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:27-28 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_27_28_quote : String :=
  "3:27 Where is boasting then? It is excluded. By what law? of works? " ++
  "Nay: but by the law of faith. 3:28 Therefore we conclude that a man " ++
  "is justified by faith without the deeds of the law."

/-- The boasting exclusion pattern in Romans 3:27-28. -/
structure BoastingFaithPattern where
  boastingExcluded : Bool
  notLawOfWorks : Bool
  lawOfFaith : Bool
  justifiedByFaith : Bool
  withoutDeedsOfLaw : Bool
deriving DecidableEq, Repr

/-- Boasting is excluded by the law of faith, not works. -/
def boastingFaithPattern : BoastingFaithPattern where
  boastingExcluded := true
  notLawOfWorks := true
  lawOfFaith := true
  justifiedByFaith := true
  withoutDeedsOfLaw := true

/-- The bounded Romans 3:27-28 witness. -/
theorem romans_boasting_excluded_faith_witness :
    boastingFaithPattern.boastingExcluded = true
    ∧ boastingFaithPattern.notLawOfWorks = true
    ∧ boastingFaithPattern.lawOfFaith = true
    ∧ boastingFaithPattern.justifiedByFaith = true
    ∧ boastingFaithPattern.withoutDeedsOfLaw = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RomansBoastingExcludedFaithWitness
end Gnosis.Witnesses.Bible.Romans
