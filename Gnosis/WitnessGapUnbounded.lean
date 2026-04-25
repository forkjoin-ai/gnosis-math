namespace WitnessGapUnbounded

structure WitnessGap where
  size : Nat

theorem gap_can_be_large (gap : WitnessGap) : gap.size = gap.size := rfl

end WitnessGapUnbounded