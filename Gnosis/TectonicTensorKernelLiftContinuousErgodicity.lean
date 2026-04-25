namespace TectonicTensorKernelLiftContinuousErgodicity

structure TensorKernel where
  lift_dimension : Nat
  ergodicity_measure : Nat
  continuous_lift : ergodicity_measure ≥ lift_dimension

theorem lift_implies_ergodicity (k : TensorKernel) :
  k.ergodicity_measure ≥ k.lift_dimension := by
  exact k.continuous_lift

end TectonicTensorKernelLiftContinuousErgodicity