/-!
# Blob Hypothesis Sketch

Init-only `(β₀, β₁)` signature witnesses for cohesive blob versus fragmented
plume descriptions.
-/

namespace PlanetaryHomologySandbox

structure BettiSignature where
  beta0 : Nat
  beta1 : Nat
deriving Repr, DecidableEq

def blobCohesive (sig : BettiSignature) : Prop :=
  sig.beta0 = 1

def plumeFragmented (sig : BettiSignature) : Prop :=
  2 ≤ sig.beta0

theorem not_plumeFragmented_of_blobCohesive
    (sig : BettiSignature)
    (hBlob : blobCohesive sig) :
    ¬ plumeFragmented sig := by
  intro hPlume
  unfold blobCohesive at hBlob
  unfold plumeFragmented at hPlume
  rw [hBlob] at hPlume
  contradiction

end PlanetaryHomologySandbox
