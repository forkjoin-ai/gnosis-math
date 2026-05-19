import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansRaisedForJustificationWitness

/-!
# Romans 4:23-25 (KJV) -- Raised for Our Justification

This unit gives one bounded "for us also" topology:

  * imputation was not written for Abraham's sake alone;
  * it is for those who believe on the one who raised Jesus our Lord from the dead;
  * Jesus was delivered for offences;
  * Jesus was raised again for justification.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 4:23-25 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_4_23_25_quote : String :=
  "4:23 Now it was not written for his sake alone, that it was imputed " ++
  "to him; 4:24 But for us also, to whom it shall be imputed, if we " ++
  "believe on him that raised up Jesus our Lord from the dead; 4:25 Who " ++
  "was delivered for our offences, and was raised again for our " ++
  "justification."

/-- The closing imputation and resurrection pattern in Romans 4:23-25. -/
structure RaisedForJustificationPattern where
  notWrittenForHisSakeAlone : Bool
  writtenForUsAlso : Bool
  imputedToBelievers : Bool
  believeOnRaiserOfJesus : Bool
  jesusDeliveredForOffences : Bool
  jesusRaisedForJustification : Bool
deriving DecidableEq, Repr

/-- The imputation pattern extends to believers in the raiser of Jesus. -/
def raisedForJustificationPattern : RaisedForJustificationPattern where
  notWrittenForHisSakeAlone := true
  writtenForUsAlso := true
  imputedToBelievers := true
  believeOnRaiserOfJesus := true
  jesusDeliveredForOffences := true
  jesusRaisedForJustification := true

/-- The bounded Romans 4:23-25 witness. -/
theorem romans_raised_for_justification_witness :
    raisedForJustificationPattern.notWrittenForHisSakeAlone = true
    ∧ raisedForJustificationPattern.writtenForUsAlso = true
    ∧ raisedForJustificationPattern.imputedToBelievers = true
    ∧ raisedForJustificationPattern.believeOnRaiserOfJesus = true
    ∧ raisedForJustificationPattern.jesusDeliveredForOffences = true
    ∧ raisedForJustificationPattern.jesusRaisedForJustification = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansRaisedForJustificationWitness
end Gnosis.Witnesses.Bible.Romans
