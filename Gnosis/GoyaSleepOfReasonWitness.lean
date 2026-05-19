import Init

/-
  GoyaSleepOfReasonWitness.lean
  =============================

  Francisco de Goya y Lucientes (1746–1828). This witness names two image floors
  the operator grouped: the late “Black Paintings” (house murals, ~1819–1823
  — dating is scholarship-dependent) and *Los desastres de la guerra*
  (Disasters of War, etched ~1810–1820, bulk published 1863).

  Hard-culture floor (in-repo English): the systemic nightmare — default
  logic of the void when the operator treats reason as if it
  could idle without cost.

  Quotation (*Los Caprichos*, plate 43, Spanish with one English gloss):

    *El sueño de la razón produce monstruos.*

    “The sleep of reason produces monsters.”

  Mencken-style reduction (prose tag, not a proof about history): Reason maps
  here to a resource-intensive process that must be actively
  maintained — not a permanent idle guarantee. When the processor
  idles (“sleep”), the system does not stay empty; it reverts
  to legacy code — monsters named in operator layer as
  superstition, violence, and the “Sadeian” impulse (compare
  `SadeSolipsismThesisRejectedWitness` for the repository stance on Sade —
  this file does not import that thesis).

  The Sleep: suspension of the “Orwellian” commitment to objective
  fact speech — parallel tag to `OrwellNineteenEightyFourWitness`
  (bedrock arithmetic there stays proved; permission / policy
  tags remain yours).

  The Monsters: emergent entities filling the vacuum — not
  modeled as wholly “external” threats in this witness,
  but as internal subroutines that run when the logic kernel
  is offline (image / systems metaphor only).

  Repo cousins: `FuckNazis` (repetition / mass belief
  hazard — different century, shared nightmare imagery); `MenckenConscienceShadowWitness` (social telemetry reduction
  — different variable, shared skepticism toward folk Enlightenment
  costumes); `OrwellNineteenEightyFourWitness` (fact speech floor); `SadeSolipsismThesisRejectedWitness`
  (named impulse branch in operator gloss — rejected thesis
  there); `BaconVelazquezPopeStudiesWitness` (nervous machine in crisis
  — later accent, different medium); `BoschGardenEarthlyDelightsWitness`
  (consequence network in one triptych — pre-Enlightenment
  accent, different tag set than sleep / monsters here).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace GoyaSleepOfReasonWitness

/-- Tag: reason as maintained process (cost / vigilance) — you discharge. -/
abbrev reasonAsMaintenanceProcess (claim : Prop) : Prop :=
  claim

/-- Tag: idle “processor” → legacy shapes / monsters (systems metaphor). -/
abbrev idleProcessorLegacyMonsters (claim : Prop) : Prop :=
  claim

/-- Tag: sleep of reason as suspension of bedrock-fact commitment (policy layer). -/
abbrev sleepSuspendsFactCommitment (claim : Prop) : Prop :=
  claim

/-- Tag: monsters as internal subroutines in vacuum fill (image register). -/
abbrev monstersAsInternalSubroutines (claim : Prop) : Prop :=
  claim

/--
  Systemic nightmare bundle: maintenance burden + legacy fill +
  sleep tag + internal monster subroutines.
-/
structure SystemicNightmareWitness (maintain idle sleep internal : Prop) where
  process : reasonAsMaintenanceProcess maintain
  legacy : idleProcessorLegacyMonsters idle
  suspended : sleepSuspendsFactCommitment sleep
  subroutines : monstersAsInternalSubroutines internal

theorem nightmare_conjuncts (M I S N : Prop) (w : SystemicNightmareWitness M I S N) :
    M ∧ I ∧ S ∧ N :=
  And.intro w.process (And.intro w.legacy (And.intro w.suspended w.subroutines))

def buildNightmareWitness (M I S N : Prop) (hM : M) (hI : I) (hS : S) (hN : N) :
    SystemicNightmareWitness M I S N :=
  ⟨hM, hI, hS, hN⟩

/--
  Caprichos plate hook alone: sleep produces monsters (two tags).
-/
structure SleepProducesMonstersWitness (sleepClaim monsterClaim : Prop) where
  sleepTag : sleepSuspendsFactCommitment sleepClaim
  monsterTag : idleProcessorLegacyMonsters monsterClaim

end GoyaSleepOfReasonWitness
