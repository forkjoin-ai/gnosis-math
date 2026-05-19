import Init

/-
  BaconVelazquezPopeStudiesWitness.lean
  =====================================

  Francis Bacon (1909–1992), *Study after Velázquez’s Portrait of Pope Innocent X* and
  related variations (1950s — dating varies by canvas). Hard-culture floor
  (in-repo English): the kinetic agony of the nervous system — biological
  machine in crisis — after Balthus’s crystalline stasis (`BalthusGeometricStasisWitness`:
  opaque closure vs screaming flesh).

  Quotation (one English gloss of Bacon’s interview language):

    “I want to do very widespread things… to paint the scream more than the horror.”

  Subversion — scream over horror: the image targets the felt vibration
  of panic (the scream) rather than illustrating gore as spectacle —
  not a medical claim; a witness to painterly priority.

  Velázquez scaffold: the Pope silhouette survives as citation while the
  figure dissolves into twitch / blur — dialogue with Spanish baroque
  authority without importing art history into Lean.

  Repo cousins: `LostSheepParableWitness` (fold as mass caricature vs
  one straggler — theological parable only rhymes with flesh
  crisis here); `GoyaSleepOfReasonWitness` (systemic nightmare / void fill
  — earlier Spanish floor, different accent than nervous kinetic
  crisis here); `BalthusGeometricStasisWitness` (stasis vs kinetic crisis);
  `MagritteTheSurvivorWitness` (object charge — different affect); `ElGrecoElasticRealWitness`
  (body under sacred stretch); `CamusMythOfSisyphusWitness` (vitality / alarm —
  distant kin); `BeckettUnnamableWitness` (loop without rebate — different medium).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace BaconVelazquezPopeStudiesWitness

/-- Tag: kinetic agony — nervous system as machine in crisis (you discharge). -/
abbrev nervousSystemKineticAgony (claim : Prop) : Prop :=
  claim

/-- Tag: biological machine under stress / failure mode (image register). -/
abbrev biologicalMachineInCrisis (claim : Prop) : Prop :=
  claim

/-- Tag: scream prioritized over horror illustration (quotation’s pivot). -/
abbrev screamMoreThanHorror (claim : Prop) : Prop :=
  claim

/-- Tag: study after Velázquez Pope — cited armature + dissolved figure. -/
abbrev velazquezPopeScaffold (claim : Prop) : Prop :=
  claim

/--
  Pope studies bundle: agony + machine crisis + scream-first painting.
-/
structure PopeStudyCrisisWitness (agony machine scream : Prop) where
  kinetic : nervousSystemKineticAgony agony
  biology : biologicalMachineInCrisis machine
  priority : screamMoreThanHorror scream

theorem crisis_conjuncts (A M S : Prop) (w : PopeStudyCrisisWitness A M S) : A ∧ M ∧ S :=
  And.intro w.kinetic (And.intro w.biology w.priority)

def buildCrisisWitness (A M S : Prop) (hA : A) (hM : M) (hS : S) : PopeStudyCrisisWitness A M S :=
  ⟨hA, hM, hS⟩

/--
  Optional fourth tag: Velázquez citation layer alone.
-/
structure VelazquezArmatureWitness (armature : Prop) where
  cited : velazquezPopeScaffold armature

end BaconVelazquezPopeStudiesWitness
