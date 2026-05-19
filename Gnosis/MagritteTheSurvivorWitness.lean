import Init

/-
  MagritteTheSurvivorWitness.lean
  ================================

  René Magritte, *Le Survivant* / *The Survivor* (1950, Brussels — one standard
  reading of the upright rifle and dark pool at its foot as blood on the
  hardware). Jungian inversion of guilt (prose tag): usually the agent who
  fires wears the blood; here the biological consequence is transferred
  onto the object — projection / participation mystique vocabulary maps to
  Jung’s object-bearing affect without claiming this canvas proves analytic
  theory (`JungAionShadowSuppressionWitness`).

  The rifle: no longer only a tool of Machiavellian utility (compare
  `MachiavelliPrinceOughtIsWitness` — Is of power / means-end honesty); the image
  treats steel as if it bore agency — bleeding for its own function
  (witness metaphor, not armorer’s physics).

  The blood: read as a Mencian reflex idiom on inanimate hardware — the
  thing “flinches” / “weeps” at its own kinetic output (`MenciusChildAtWellWitness`
  — alarm on harm transposed to object skin; not Mengzi’s text,
  same reflex shape in the witness stack).

  Repo cousins: `BalthusGeometricStasisWitness` (opaque stasis vs charged
  hardware — different autonomy geometry);
  `MagritteTreacheryOfImagesWitness` (same artist, 1929 semiotic floor);
  `JungAionShadowSuppressionWitness` (projection / hidden charge); `MachiavelliPrinceOughtIsWitness`;
  `MenciusChildAtWellWitness`; `DuchampRetinalTrapWitness` (object gains type from frame —
  different gesture).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace MagritteTheSurvivorWitness

/-- Tag: guilt / blood transferred onto hardware (not only on the shooter’s hands). -/
abbrev bloodOnHardwareNotOnlyAgent (claim : Prop) : Prop :=
  claim

/-- Tag: rifle as non-instrumental “agent” — bleeds for its function (image logic). -/
abbrev rifleAsBleedingAgent (claim : Prop) : Prop :=
  claim

/-- Tag: Mencian-style reflex read onto inanimate kinetic output (flinch / weep). -/
abbrev bloodAsMencianReflexOnThing (claim : Prop) : Prop :=
  claim

/--
  Survivor bundle: hardware bears consequence + rifle agency metaphor + reflex on thing.
-/
structure SurvivorInversionWitness (hardware rifleThing reflex : Prop) where
  bloodTransferred : bloodOnHardwareNotOnlyAgent hardware
  agenticRifle : rifleAsBleedingAgent rifleThing
  mencianSkin : bloodAsMencianReflexOnThing reflex

theorem survivor_conjuncts (H R M : Prop) (w : SurvivorInversionWitness H R M) : H ∧ R ∧ M :=
  And.intro w.bloodTransferred (And.intro w.agenticRifle w.mencianSkin)

def buildSurvivorWitness (H R M : Prop) (hH : H) (hR : R) (hM : M) : SurvivorInversionWitness H R M :=
  ⟨hH, hR, hM⟩

end MagritteTheSurvivorWitness
