namespace ContrarianWitnessGapAmplifiesClarity

structure WitnessState where
  has_gap : Prop
  amplifies_clarity : Prop

theorem gap_is_clarity (w : WitnessState) (h : w.has_gap → w.amplifies_clarity) (hg : w.has_gap) : w.amplifies_clarity := h hg

end ContrarianWitnessGapAmplifiesClarity