namespace ContrarianTransparencyIncreasesFraud

structure TransparencyFraudAdapter where
  system_transparency : Nat
  adversarial_adaptation : Nat
  fraud_surface_area : Nat
  h_fraud : fraud_surface_area = system_transparency * adversarial_adaptation + system_transparency

theorem fraud_surface_increases_with_transparency (adapter : TransparencyFraudAdapter) :
  adapter.fraud_surface_area ≥ adapter.system_transparency := by
  rw [adapter.h_fraud]
  exact Nat.le_add_left adapter.system_transparency (adapter.system_transparency * adapter.adversarial_adaptation)

end ContrarianTransparencyIncreasesFraud