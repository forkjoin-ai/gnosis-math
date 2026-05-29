namespace Gnosis

structure TensegrityWitnessAssumptions where
  witnessGap : Prop
  tensegrityScaffold : Prop
  scaffoldBridgesGap : tensegrityScaffold -> witnessGap

theorem tensegrity_bridges_witness_gap (assumptions : TensegrityWitnessAssumptions) :
    assumptions.tensegrityScaffold -> assumptions.witnessGap := by
  intro h
  exact assumptions.scaffoldBridgesGap h

end Gnosis