namespace Gnosis

structure ContrarianTensegrityAssumptions where
  missingInterpretation : Prop
  tensegrityEnabled : Prop
  missingEnablesTensegrity : missingInterpretation -> tensegrityEnabled

theorem contrarian_missing_interpretation_enables_tensegrity (assumptions : ContrarianTensegrityAssumptions) :
    assumptions.missingInterpretation -> assumptions.tensegrityEnabled := by
  intro h
  exact assumptions.missingEnablesTensegrity h

end Gnosis