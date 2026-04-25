
namespace BuleyeanMath

structure TensegrityBridgeAssumptions where
  witnessGap : Prop
  tensegrityStructure : Prop
  structureFormsBridge : tensegrityStructure -> witnessGap

theorem tensegrity_forms_witness_bridge (assumptions : TensegrityBridgeAssumptions) :
    assumptions.tensegrityStructure -> assumptions.witnessGap := by
  intro h
  exact assumptions.structureFormsBridge h

end BuleyeanMath