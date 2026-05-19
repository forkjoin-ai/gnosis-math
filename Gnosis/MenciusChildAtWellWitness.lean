import Init

/-
  MenciusChildAtWellWitness.lean
  ==============================

  *Mencius* / *Mengzi* (compiled tradition; core figure Meng Ke 孟子, commonly dated
  c. 372–289 BC; the operator’s c. 300 BC hook names the classical stratum,
  not a single composition year). Hard-culture floor (in-repo English): human nature
  (xing 性 / xin 心 idiom) named as something closer to a reflex than to a
  free-floating “Spook” in Stirner’s *Spuk* sense (`StirnerEgoAndOwnWitness` — different
  project: Mengzi is not egoist; the witness layer only contrasts the billing
  of morality as pure spectral sovereignty versus an alarm that fires on
  imminent harm).

  Quotation (child-at-well passage, one standard English gloss):

    “No man is devoid of a heart sensitive to the suffering of others… if a man were
    suddenly to see a child about to fall into a well, he would without exception
    experience a feeling of alarm and distress.”

  Rumination (not a theorem): does this map morality to a startle response? In
  this file: only as a question you export — the Lean bundle below stays tags.

  Repo cousins: `LukeGoodSamaritanWitness` (roadside mercy work tagged as
  Mencian reflex idiom — different canon, shared pressure shape);
  `MagritteTheSurvivorWitness` (reflex idiom transposed onto rifle /
  blood — pictorial flinch, not the classical child-at-well proof obligation);
  `CamusMythOfSisyphusWitness` (alarm / vitality — different canon);
  `MenckenConscienceShadowWitness` (social telemetry — different reduction);
  `EpicurusTetrapharmakosWitness` (material fear-stack — different floor);
  `HeartTongueTotalNegationWitness` (organ vs speech — different ancient thread).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace MenciusChildAtWellWitness

/-- Tag: xin / heart not void of compassion for others’ suffering (you discharge). -/
abbrev heartSensitiveToOthersSuffering (claim : Prop) : Prop :=
  claim

/-- Tag: alarm and distress on seeing imminent harm to another (child-at-well). -/
abbrev startleReflexToImminentHarm (claim : Prop) : Prop :=
  claim

/-- Tag: moral floor reads as reflex / unbidden alarm, not only as abstract ghost-sovereignty. -/
abbrev moralityAsReflexNotSpookAlone (claim : Prop) : Prop :=
  claim

/--
  Bundles universality of the compassionate heart with the well startle image —
  no proof that “all ethics reduces to startle” (that would be a different `Prop`).
-/
structure ChildAtWellWitness (universalHeart wellStartle : Prop) where
  noManDevoid : heartSensitiveToOthersSuffering universalHeart
  childAtWell : startleReflexToImminentHarm wellStartle

theorem well_conjuncts (U W : Prop) (w : ChildAtWellWitness U W) : U ∧ W :=
  And.intro w.noManDevoid w.childAtWell

def buildWellWitness (U W : Prop) (hU : U) (hW : W) : ChildAtWellWitness U W :=
  ⟨hU, hW⟩

/--
  Optional third tag: “morality as startle?” — keep explicit so cynic readings cannot
  pretend this file proved the reduction.
-/
structure ReflexBillingWitness (reflexClaim spookContrast : Prop) where
  reflexFloor : moralityAsReflexNotSpookAlone reflexClaim
  notSpookOnly : spookContrast

theorem reflex_conjuncts (R S : Prop) (w : ReflexBillingWitness R S) : R ∧ S :=
  And.intro w.reflexFloor w.notSpookOnly

def buildReflexWitness (R S : Prop) (hR : R) (hS : S) : ReflexBillingWitness R S :=
  ⟨hR, hS⟩

end MenciusChildAtWellWitness
