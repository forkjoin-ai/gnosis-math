namespace CrossDomainLinguisticsEpidemiologyBridge

structure LinguisticsEpidemiologyAdapter where
  viral_load : Nat
  semantic_density : Nat
  transmission_rate : Nat
  h_transmission : transmission_rate = viral_load * semantic_density + viral_load

theorem transmission_bound (adapter : LinguisticsEpidemiologyAdapter) :
  adapter.transmission_rate ≥ adapter.viral_load := by
  rw [adapter.h_transmission]
  exact Nat.le_add_left adapter.viral_load (adapter.viral_load * adapter.semantic_density)

end CrossDomainLinguisticsEpidemiologyBridge