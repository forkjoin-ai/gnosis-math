import Init

/-
  CohenAnthemWitness.lean
  =======================

  Leonard Cohen (1934–2016), “Anthem” (released 1992 on *The Future* — dating
  follows the operator’s release-year hook).

  Hard-culture floor (in-repo English): perfectionism — the demand for a
  sealed, blameless offering before motion is permitted — and
  the counter-move that maps imperfection to ingress (light through
  crack), not as a license for sloppy work in this repository,
  but as a psychological / spiritual tag you discharge elsewhere.

  Quotation (refrain, English as commonly printed on lyric sheets):

    “Forget your perfect offering /
    There is a crack, a crack in everything /
    That’s how the light gets in.”

  Subversion: actions need not wait on a closed ideal form;
  brokenness indexes a channel — parallel metaphor to void-as-use
  in `LaoziBowlVoidFunctionWitness`, different medium and tone.

  Proved toy (Init only): `crack_has_positive_width` witnesses a strict
  `0 < 1` step — a minimal positive “width” for ingress in
  order arithmetic only; not optics or soul claims.

  Repo cousins: `WildeDecayOfLyingSincerityWitness` (sincerity tyranny — adjacent
  pressure on presentation); `CamusMythOfSisyphusWitness` (struggle without
  cheap closure — different remedy); `CioranTroubleWithBeingBornWitness`
  (decay mood — tension: Cohen’s crack tags ingress, not terminal
  void-loyalty); `LaoziBowlVoidFunctionWitness` (useful null — structural
  rhyme only); `JoplinMeAndBobbyMcGeeWitness` (“nothing left to lose”
  freedom gloss — different register than crack/light here); `BukowskiWalkThroughFireWitness`
  (ordeal as meter — fire walk, different image than crack/light
  here).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace CohenAnthemWitness

/-- Tag: perfectionism as hard floor / block (you discharge). -/
abbrev perfectionismHardFloor (claim : Prop) : Prop :=
  claim

/-- Tag: permission to release “perfect offering” fantasy before acting. -/
abbrev forgetPerfectOffering (claim : Prop) : Prop :=
  claim

/-- Tag: crack in everything → light ingress (image register). -/
abbrev crackAdmitsLight (claim : Prop) : Prop :=
  claim

/--
  Anthem bundle: floor + release + crack/light.
-/
structure AnthemPerfectionismWitness (floor release ingress : Prop) where
  block : perfectionismHardFloor floor
  unclench : forgetPerfectOffering release
  channel : crackAdmitsLight ingress

theorem anthem_conjuncts (F R I : Prop) (w : AnthemPerfectionismWitness F R I) : F ∧ R ∧ I :=
  And.intro w.block (And.intro w.unclench w.channel)

def buildAnthemWitness (F R I : Prop) (hF : F) (hR : R) (hI : I) : AnthemPerfectionismWitness F R I :=
  ⟨hF, hR, hI⟩

/-- Toy: one-step positive width for a “crack” in minimal `Nat` order (not measurement theory). -/
theorem crack_has_positive_width : (0 : Nat) < 1 :=
  Nat.zero_lt_succ 0

end CohenAnthemWitness
