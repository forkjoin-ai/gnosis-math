namespace BuleyeanMath

structure LatentWitness where
  absenceCount : Nat

theorem latent_witness_absence_optimal (w : LatentWitness) (h : w.absenceCount = 0) : w.absenceCount < 1 := by
  omega

end BuleyeanMath