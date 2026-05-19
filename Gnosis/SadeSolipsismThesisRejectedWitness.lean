import Init

/-
  SadeSolipsismThesisRejectedWitness.lean
  =======================================

  Marquis de Sade, *Les 120 Journées de Sodome* / *The 120 Days of Sodom* (composed
  1785; publication history is fraught — this file is not a literary endorsement),
  materialist line (one English gloss used in scholarship):

    “There is no god, nature sufficeth unto herself; in no wise hath she need of an
    author.”

  Repository stance — this one is provably wrong (in-repo): whatever “hard
  culture” reading one might extract, the Sadean solipsism-of-sensation package that
  treats the Other as a peripheral device and moral concern for another’s
  suffering as a logic error is rejected here. Epicurus retires divine
  operators on physics; that does not entail erasing other subjects as real.
  Stirner’s *Spuk* cutting targets false sovereign abstractions; it is not
  a license to deny that other nerves are morally salient. Nature is not
  licensed in this repository as a moral mandate for indifferent destruction.

  Formal straw (refutation only): we model “no other exists / nothing counts but my
  sensation” as the obviously inconsistent predicate `∀ (_ : Unit), False` — there is
  at least one index (`Unit`) so total negation of otherhood cannot hold. This is
  a toy inconsistency proof, not anthropology; it exists so “provably wrong” is not
  empty rhetoric inside Lean.

  Affirmation cousin (rejects Sade’s “no god” fork only): `GodAndNatureSufficientWitness`
  — there is a God and nature is enough unto herself, as a conjunction witness,
  not as endorsement of Sade’s sequel.

  Still isolation (shape without Sade ethics): `BalthusGeometricStasisWitness` — crystalline
  stasis / opaque subject; not the Sadean solipsism thesis rejected
  here, but the word “Sadeian” isolates a formal loneliness rhyme only.

  Psychological contrast (not endorsement of Sade ethics): `JungAionShadowSuppressionWitness`
  — Jung’s “hard culture” pivot targets suppression and the hidden stratum; that
  names a different hazard than treating Sade’s “engine” as a how-to manual.

  Repo cousins (contrast, not lineage): `EpicurusTetrapharmakosWitness`;
  `StirnerEgoAndOwnWitness`; `HobbesLeviathanStateOfNatureWitness` (common power vs
  private war); `HeartTongueTotalNegationWitness` (interface myths — different moral);
  `GoyaSleepOfReasonWitness` (operator gloss names a “Sadeian” impulse
  among “monsters” when reason idles — this file still
  rejects Sade’s thesis as stated above).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace SadeSolipsismThesisRejectedWitness

/-- Straw formalization: “no other index even exists for moral salience.” -/
def isolatedSensoriumStraw : Prop :=
  ∀ _ : Unit, False

/-- The straw solipsism predicate is inconsistent (at least one `Unit` witness). -/
theorem isolated_sensorium_straw_is_false : ¬ isolatedSensoriumStraw := by
  intro h
  exact h ()

end SadeSolipsismThesisRejectedWitness
