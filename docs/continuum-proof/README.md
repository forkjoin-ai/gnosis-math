# Continuum proof: SU(2) -> SO(3) (Mathlib companion)

Preserved SOURCE of the continuous double-cover proof. This is a SEPARATE Mathlib
Lake project — it deliberately does NOT live in the Init-only `Gnosis` ledger (adding
Mathlib would re-point the ledger's default target at the classical-Real "cathedral"
the sovereign ledger refuses). Keep it quarantined here as source; reconstitute to build.

## What it proves (verified green, `#print axioms` = [propext, Classical.choice, Quot.sound], 0 sorry)
- `rho q v = q * v * star q` (Mathlib `Quaternion ℝ` conjugation)
- (i) homomorphism: `rho_one`, `rho_mul`
- (ii) KERNEL = {±1}: `kernel_eq_pm_one` (the continuous lift of the discrete `square_loses_sign`)
- (iii) periodicity: `loop_two_pi = -1`, `loop_four_pi = 1`, `rho_loop_two_pi` (rotation returns at 2pi, spinor at 4pi)
- master: `su2_so3_continuous_cover_core`
- (iv) surjectivity onto SO(3): OPEN (axis-angle), no sorry.

Discrete shadow: `Gnosis.OrientationSpinorBridge` (Init-only). This is its continuous lift.

## Rebuild
    cp -r . /tmp/spinor-continuum && cd /tmp/spinor-continuum
    lake exe cache get      # pulls ~8459 prebuilt Mathlib oleans (minutes, no source build)
    lake build              # SpinorContinuum builds against cached Mathlib
Toolchain: leanprover/lean4:v4.30.0, Mathlib tag v4.30.0.

## Impl note
`(-1 : Quaternion ℝ)` does not match `neg_one_mul`/`mul_neg_one` directly; use
`rw [neg_one_mul v, neg_mul_comm, neg_neg, mul_one]`; noncommutative associativity needs `noncomm_ring`.
