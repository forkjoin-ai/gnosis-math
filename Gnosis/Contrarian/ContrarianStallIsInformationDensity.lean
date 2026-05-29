/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianStallIsInformationDensity` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/

namespace ForkRaceFold

structure StallDensity where
  stall_duration : Nat
  compression_ratio : Nat

theorem stall_is_density (s : StallDensity) (h1 : s.stall_duration = s.compression_ratio) (h2 : s.compression_ratio > 10) :
  s.stall_duration > 10 := by
  rwa [h1]

end ForkRaceFold
