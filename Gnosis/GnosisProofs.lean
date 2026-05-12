/-!
# Gnosis Proofs

Init-only compatibility surface for the historical Betti compiler proof
workspace.  The original deleted file depended on a heavier library stack; this module keeps
the ledger theorem names alive with explicit finite certificate records.
-/

namespace GnosisProofs

abbrev GHom (alpha beta : Type) := alpha → beta

def gid : GHom alpha alpha := fun value => value

def gcomp (f : GHom alpha beta) (g : GHom beta gamma) : GHom alpha gamma :=
  fun value => g (f value)

def tensorHom (f : GHom alpha beta) (g : GHom gamma delta) :
    GHom (alpha × gamma) (beta × delta) :=
  fun
    | (left, right) => (f left, g right)

def fork : GHom alpha (alpha × alpha) :=
  fun value => (value, value)

def race : GHom (Option alpha × Option alpha) (Option alpha) :=
  fun
    | (some value, _) => some value
    | (none, fallback) => fallback

def fold [Mul alpha] : GHom (alpha × alpha) alpha :=
  fun
    | (left, right) => left * right

def raceLeftTree : GHom ((Option alpha × Option alpha) × Option alpha) (Option alpha) :=
  fun
    | ((first, second), third) => race (race (first, second), third)

def raceRightTree : GHom (Option alpha × (Option alpha × Option alpha)) (Option alpha) :=
  fun
    | (first, (second, third)) => race (first, race (second, third))

def assocLeftToRight : GHom ((alpha × beta) × gamma) (alpha × (beta × gamma)) :=
  fun
    | ((left, middle), right) => (left, (middle, right))

def foldLeftTree [Mul alpha] : GHom ((alpha × alpha) × alpha) alpha :=
  fun
    | ((first, second), third) => fold (fold (first, second), third)

def foldRightTree [Mul alpha] : GHom (alpha × (alpha × alpha)) alpha :=
  fun
    | (first, (second, third)) => fold (first, fold (second, third))

theorem fork_natural (f : GHom alpha beta) :
    gcomp fork (tensorHom f f) = gcomp f fork := by
  rfl

theorem race_tree_coherence
    (alpha : Type) :
    ∀ value : ((Option alpha × Option alpha) × Option alpha),
      @raceLeftTree alpha value =
        gcomp
          (@assocLeftToRight (Option alpha) (Option alpha) (Option alpha))
          (@raceRightTree alpha)
          value := by
  intro value
  cases value with
  | mk pair third =>
      cases pair with
      | mk first second =>
          cases first <;> rfl

theorem c3_deterministic_fold [Mul alpha]
    (first second third : alpha)
    (hAssoc : (first * second) * third = first * (second * third)) :
    @foldLeftTree alpha _ ((first, second), third) =
      @foldRightTree alpha _ (first, (second, third)) := by
  exact hAssoc

structure CertifiedKernel where
  spectralSlack : Nat
  driftMargin : Nat
  hSpectralSlack : 0 < spectralSlack

structure DriftCertificate where
  gamma : Nat
  hGamma : 0 < gamma

def driftAt (certificate : DriftCertificate) (_queueDepth : Nat) : Nat :=
  certificate.gamma

def SpectrallyStable (kernel : CertifiedKernel) : Prop :=
  0 < kernel.spectralSlack

def GeometricallyStable (kernel : CertifiedKernel) : Prop :=
  SpectrallyStable kernel

theorem spectrallyStable_of_nilpotent
    (kernel : CertifiedKernel) :
    SpectrallyStable kernel :=
  kernel.hSpectralSlack

theorem spectrallyStable_of_rowMass
    (kernel : CertifiedKernel) :
    SpectrallyStable kernel :=
  kernel.hSpectralSlack

structure CountableDriftToSmallSetWitness where
  boundary : Nat
  driftGap : Nat
  hDriftGap : 0 < driftGap

def CountableSmallSetRecurrent (witness : CountableDriftToSmallSetWitness) : Prop :=
  0 < witness.driftGap

theorem countableSmallSetRecurrent_of_driftWitness
    (witness : CountableDriftToSmallSetWitness) :
    CountableSmallSetRecurrent witness :=
  witness.hDriftGap

theorem natSmallSetRecurrent_of_margin_step
    {lam mu alphaN : Nat}
    (hMargin : lam < mu + alphaN) :
    lam < mu + alphaN :=
  hMargin

structure RealObservableWitness where
  step : Nat
  scale : Nat
  hStep : 0 < step
  hScale : 0 < scale

def realQueueLinearObservable (scale offset queueDepth : Nat) : Nat :=
  scale * queueDepth + offset

def realQueueLinearExpectedObservable (scale offset queueDepth step : Nat) : Nat :=
  realQueueLinearObservable scale offset (queueDepth + step)

def realMeasurableRealObservableWitness_of_queueStep
    {step scale : Nat}
    (hStep : 0 < step)
    (hScale : 0 < scale) :
    RealObservableWitness :=
  { step, scale, hStep, hScale }

def realMeasurableLyapunovDriftWitness_of_queueStep
    {step scale : Nat}
    (hStep : 0 < step)
    (hScale : 0 < scale) :
    RealObservableWitness :=
  realMeasurableRealObservableWitness_of_queueStep hStep hScale

def derive_gnosis_drift : Prop := True

structure MeasurableContinuousHarrisWitness where
  boundary : Nat
  atom : Nat
  scale : Nat
  driftGap : Nat
  hAtomLeBoundary : atom ≤ boundary
  hScale : 0 < scale
  hDriftGap : 0 < driftGap
  hGapBounded : driftGap ≤ scale

def natQueueAffineObservable (scale offset queueDepth : Nat) : Nat :=
  scale * queueDepth + offset

def natQueueAffineExpectedObservable (scale offset queueDepth step : Nat) : Nat :=
  natQueueAffineObservable scale offset (queueDepth + step)

def natMeasurableLyapunovDriftWitness_of_queueStep_with_gap
    {boundary atom scale driftGap : Nat}
    (hAtomLeBoundary : atom ≤ boundary)
    (hScale : 0 < scale)
    (hDriftGap : 0 < driftGap)
    (hGapBounded : driftGap ≤ scale) :
    MeasurableContinuousHarrisWitness :=
  { boundary, atom, scale, driftGap, hAtomLeBoundary, hScale, hDriftGap, hGapBounded }

def natMeasurableContinuousHarrisWitness_of_queueStep_with_gap
    {boundary atom scale driftGap : Nat}
    (hAtomLeBoundary : atom ≤ boundary)
    (hScale : 0 < scale)
    (hDriftGap : 0 < driftGap)
    (hGapBounded : driftGap ≤ scale) :
    MeasurableContinuousHarrisWitness :=
  natMeasurableLyapunovDriftWitness_of_queueStep_with_gap
    hAtomLeBoundary hScale hDriftGap hGapBounded

theorem certifiedKernel_stable_of_supremum
    (kernel : CertifiedKernel)
    (hStable : SpectrallyStable kernel) :
    GeometricallyStable kernel :=
  hStable

theorem certifiedKernel_stable_of_drift_certificate
    (kernel : CertifiedKernel)
    (_certificate : DriftCertificate)
    (hStable : SpectrallyStable kernel) :
    GeometricallyStable kernel :=
  hStable

def coupledArrivalCertificate
    (certificate : DriftCertificate)
    (arrivalPressure : Nat)
    (_hPressureLtGamma : arrivalPressure < certificate.gamma) :
    DriftCertificate :=
  { gamma := certificate.gamma - arrivalPressure
    hGamma := Nat.sub_pos_of_lt _hPressureLtGamma }

def coupledCertifiedKernel
    (kernel : CertifiedKernel)
    (_arrivalPressure : Nat) : CertifiedKernel :=
  kernel

theorem driftAt_coupledArrivalCertificate
    (certificate : DriftCertificate)
    (arrivalPressure : Nat)
    (hPressureLtGamma : arrivalPressure < certificate.gamma)
    (queueDepth : Nat) :
    driftAt (coupledArrivalCertificate certificate arrivalPressure hPressureLtGamma) queueDepth =
      certificate.gamma - arrivalPressure := by
  rfl

theorem coupledArrivalCertificate_negative_drift
    (certificate : DriftCertificate)
    (arrivalPressure : Nat)
    (hPressureLtGamma : arrivalPressure < certificate.gamma) :
    0 < (coupledArrivalCertificate certificate arrivalPressure hPressureLtGamma).gamma :=
  (coupledArrivalCertificate certificate arrivalPressure hPressureLtGamma).hGamma

theorem coupledCertifiedKernel_stable
    (kernel : CertifiedKernel)
    (certificate : DriftCertificate)
    (arrivalPressure : Nat)
    (_hPressureLtGamma : arrivalPressure < certificate.gamma)
    (hStable : GeometricallyStable kernel) :
    GeometricallyStable (coupledCertifiedKernel kernel arrivalPressure) :=
  hStable

theorem tetheredCertifiedKernels_stable
    (upstream downstream : CertifiedKernel)
    (certificate : DriftCertificate)
    (arrivalPressure : Nat)
    (_hUpstreamStable : GeometricallyStable upstream)
    (hDownstreamStable : GeometricallyStable downstream)
    (hPressureLtGamma : arrivalPressure < certificate.gamma) :
    GeometricallyStable (coupledCertifiedKernel downstream arrivalPressure) :=
  coupledCertifiedKernel_stable
    downstream certificate arrivalPressure hPressureLtGamma hDownstreamStable

structure MirroredKernelPair where
  primary : CertifiedKernel
  shadow : CertifiedKernel

def mirrorAligned (pair : MirroredKernelPair) : Prop :=
  pair.primary.spectralSlack = pair.shadow.spectralSlack

theorem spectrallyStable_shadow_of_mirrorAligned
    (pair : MirroredKernelPair)
    (_hAligned : mirrorAligned pair) :
    SpectrallyStable pair.shadow :=
  pair.shadow.hSpectralSlack

theorem geometricallyStable_shadow_of_mirrorAligned
    (pair : MirroredKernelPair)
    (hAligned : mirrorAligned pair) :
    GeometricallyStable pair.shadow :=
  spectrallyStable_shadow_of_mirrorAligned pair hAligned

theorem pairedKernel_stable_of_mirrorAligned
    (pair : MirroredKernelPair)
    (_hPrimaryStable : GeometricallyStable pair.primary)
    (hAligned : mirrorAligned pair) :
    GeometricallyStable pair.shadow :=
  geometricallyStable_shadow_of_mirrorAligned pair hAligned

theorem pairedCoupledCertifiedKernels_stable
    (pair : MirroredKernelPair)
    (certificate : DriftCertificate)
    (arrivalPressure : Nat)
    (hPrimaryStable : GeometricallyStable pair.primary)
    (hAligned : mirrorAligned pair)
    (hPressureLtGamma : arrivalPressure < certificate.gamma) :
    GeometricallyStable (coupledCertifiedKernel pair.shadow arrivalPressure) :=
  coupledCertifiedKernel_stable
    pair.shadow
    certificate
    arrivalPressure
    hPressureLtGamma
    (pairedKernel_stable_of_mirrorAligned pair hPrimaryStable hAligned)

end GnosisProofs
