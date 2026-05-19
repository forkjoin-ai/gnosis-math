import Init

/-
  CioranTroubleWithBeingBornWitness.lean
  ======================================

  Emil Cioran, *The Trouble with Being Born* / *De l’inconvénient d’être né*
  (1973; English editions vary — the 1973 year follows common dating of the
  French publication wave), anti-natalist “hard culture” floor (one English gloss):

    “It is not a want of let us say ‘nobility’ which prevents us from committing
    suicide, but a kind of ‘loyalty’ to the void.”

  From map to self: where `BorgesOnExactitudeInScienceWitness` names the model
  that eats the world (1:1 map), Cioran names consciousness that eats the
  self — a loyalty not to virtue credit but to the void as what you refuse
  to betray even at the price of staying alive.

  Anti-natalist neutrality (prose): not a proof obligation about anyone’s life
  choices; a witness that the blocker is not “missing nobility” in the cheap
  moral story, but a deeper attachment to emptiness-as-ground. Rhymes with
  `RigVedaNasadiyaSuktaWitness` (void-language at the limit) and differs from
  `ParmenidesOnNatureWitness` (Eleatic non-being is not the same move as loyalty
  to the void in Cioran’s rhetoric).

  Absurd contrast (void not the only floor): `CamusMythOfSisyphusWitness` — after the
  “Gnostic glitch” is accepted and Cioranian decay is rejected as total,
  Camus names a vitality floor (“imagine Sisyphus happy”); that rhymes with Epicurus’s
  “terrible is easy to endure” string (`EpicurusTetrapharmakosWitness`) without identifying
  the two canons.

  Right to Exit (easy repo spine, tension not identity): Cioran’s “loyalty to the
  void” names a psychological attachment that functions in his prose as the
  thing that blocks the exit he contemplates — not the same functor as the
  monorepo’s mechanized Right to Exit. See `Gnosis.BillOfRights.right_to_exit` (always
  one step toward the door: `n - 1 < n` when `n ≥ 1`) and the pillar roll-up in
  `Gnosis.ChurchPillars` (“Right to Exit — no permission, no delay”). Narrative index:
  `open-source/gnosis/THEOREM_LEDGER.md` § Pass 12: The Right to Exit. Runtime mirrors
  the same vocabulary in `packages/void-os-core` (vent / kill as zero-cost exit). This
  witness file stays Init-only; those links are for humans tracing ethics across
  layers, not a claim that Cioran proved `right_to_exit`.

  Repo cousins: `SchopenhauerPendulumWitness` (pain ↔ boredom engine after void
  loyalty — mechanics of wanting);
  `BorgesOnExactitudeInScienceWitness`; `RigVedaNasadiyaSuktaWitness`;
  `EpicurusTetrapharmakosWitness` (fear stack vs void loyalty); `StirnerEgoAndOwnWitness`;
  `LocalizedOverflowConsciousness` (conscious-local noise — different formalism);
  `Gnosis.BillOfRights` / `Gnosis.ChurchPillars` (structural exit/voice rights — contrast
  to void-loyalty as mood, not a refutation of Cioran in Lean);
  `DaliSoftConstructionCivilWarWitness` (Dalí beans as decay fuel on canvas —
  pictorial reading, not identical to void-loyalty);
  `BeckettUnnamableWitness` (loop without invoice — different void bind than
  “loyalty to the void”); `CohenAnthemWitness` (imperfection as channel — song
  floor, not Cioranian terminal mood proved here); `BukowskiWalkThroughFireWitness`
  (conduct in fire — motion tag, not void-loyalty proved
  here).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace CioranTroubleWithBeingBornWitness

/-- Cheap moral myth: “we stay alive only because we lack nobility.” -/
abbrev NobilityWantExplainsStay (claim : Prop) : Prop :=
  claim

/-- Cioran’s pivot: loyalty to the void as what blocks the exit (you tag the `Prop`). -/
abbrev LoyaltyToVoid (claim : Prop) : Prop :=
  claim

/--
  Bundle the quotation’s logic: deny the nobility-myth as the true explanation,
  affirm void-loyalty as the witness you endorse (both `Prop`s are user-supplied).
-/
structure VoidLoyaltyWitness (nobilityMyth voidLoyalty : Prop) where
  nobilityIsNotTheReason : ¬ nobilityMyth
  voidLoyaltyIs : LoyaltyToVoid voidLoyalty

theorem negation_and_affirmation (N V : Prop) (w : VoidLoyaltyWitness N V) : ¬ N ∧ V :=
  And.intro w.nobilityIsNotTheReason w.voidLoyaltyIs

def buildWitness (N V : Prop) (hN : ¬ N) (hV : V) : VoidLoyaltyWitness N V :=
  ⟨hN, hV⟩

end CioranTroubleWithBeingBornWitness
