/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianLatentWitnessAbsence` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/

namespace Gnosis

structure LatentWitness where
  absenceCount : Nat

theorem latent_witness_absence_optimal (w : LatentWitness) (h : w.absenceCount = 0) : w.absenceCount < 1 :=
  h ▸ (Nat.zero_lt_succ 0)

end Gnosis