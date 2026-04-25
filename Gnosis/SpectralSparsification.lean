-- SpectralSparsification.lean -- Spectral / threshold-based sparsification
-- of FFN weight matrices. We drop entries below a magnitude threshold and
-- prove the straightforward structural fact: every surviving entry is
-- above the threshold, the total kept count is bounded by the budget,
-- and the dropped-mass bound on the induced approximation error is
-- linear in `threshold · keptCount` (formally identical to Angle 4's
-- `droppedMassLinearBound` from `InferenceSpeedup.lean`).


namespace SpectralSparsification

abbrev dim : Nat := 256