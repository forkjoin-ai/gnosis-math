import Gnosis.GnosisTriptychBraid
import Gnosis.MonadDyadTriad

namespace Gnosis.Witnesses.Gnostic
namespace ApocryphonJohnOpeningMonadWitness

/-!
# Apocryphon of John -- Opening Monad as Anti-Idol Compiler

Source text: `docs/ebooks/source-texts/apocryphon-of-john.txt`;
text anchor `docs/ebooks/source-texts/apocryphon-of-john.txt:21-88`.

This witness deliberately does more than summarize the opening of Frederik
Wisse's Apocryphon of John. The interesting move is contrarian:

**The text does not begin with a doctrine. It begins by destroying the conditions
under which doctrine becomes an idol.**

Reading:

  * Arimanius frames the Nazarene as deception, lies, closed hearts, and betrayal of
    inherited tradition. That is the social-consensus gate.
  * John does not answer with apologetics. He exits the temple into desert grief. The
    source of knowledge is moved outside the institution before any cosmology appears.
  * The revealer appears as youth, old man, and servant, but "there was not a plurality."
    This is not trinitarian arithmetic. It is a type check: multiplicity of appearance is
    not multiplicity of source.
  * "Father / Mother / Son" is therefore not a family tree. It is a three-face interface
    for one light-form crossing the observer boundary.
  * The Monad description is mostly negation: not merely god, not bounded, not measurable,
    not nameable, not corporeal, not incorporeal, not in aeon, not in time. The passage
    refuses every capture surface before it permits predicates.
  * Only after the refusal does the positive overflow appear: life-giving, knowledge-giving,
    goodness-giving, mercy-giving, redemption-giving, grace-giving.
  * The contrarian bite: the Apocryphon's first theology is anti-theology. It compiles a
    firewall against premature naming, then allows emanation.

The mechanical witness below ties that reading to existing gnosis-math:

  * `MonadDyadTriad.monad_is_irreducible`: the Monad is treated as irreducible, not as a
    member of a class;
  * `MonadDyadTriad.triad_is_first_witness`: the three-form appearance functions as a
    witness surface, not as three gods;
  * `GnosisTriptychBraid.cycle_sum_zero`: the three-form cycle balances around zero/truth,
    matching "not plurality" despite three visible phases.

No `sorry`, no new `axiom`.
-/

inductive OpeningPhase
  | institutionalWound
  | desertExit
  | polymorphicLight
  | apophaticFirewall
  | overflowAfterNegation
deriving DecidableEq, Repr

def openingTrace : List OpeningPhase :=
  [ OpeningPhase.institutionalWound
  , OpeningPhase.desertExit
  , OpeningPhase.polymorphicLight
  , OpeningPhase.apophaticFirewall
  , OpeningPhase.overflowAfterNegation
  ]

/-- The revealer has three appearances, but the text explicitly denies
plurality. This is the formal pressure point: three faces, one source. -/
structure ThreeFaceNonPlural where
  youth : Bool
  elder : Bool
  servant : Bool
  pluralityDenied : Bool
deriving DecidableEq, Repr

def apocryphonThreeFace : ThreeFaceNonPlural where
  youth := true
  elder := true
  servant := true
  pluralityDenied := true

def threeFacesOneSource (t : ThreeFaceNonPlural) : Prop :=
  t.youth = true ∧
  t.elder = true ∧
  t.servant = true ∧
  t.pluralityDenied = true

/-- The Monad is defined first by category refusal, not by a positive idol. -/
structure ApophaticFirewall where
  notMerelyGod : Bool
  notMeasurable : Bool
  notNameable : Bool
  notCorporeal : Bool
  notIncorporeal : Bool
  outsideAeon : Bool
  outsideTime : Bool
deriving DecidableEq, Repr

def monadFirewall : ApophaticFirewall where
  notMerelyGod := true
  notMeasurable := true
  notNameable := true
  notCorporeal := true
  notIncorporeal := true
  outsideAeon := true
  outsideTime := true

def refusesCapture (f : ApophaticFirewall) : Prop :=
  f.notMerelyGod = true ∧
  f.notMeasurable = true ∧
  f.notNameable = true ∧
  f.notCorporeal = true ∧
  f.notIncorporeal = true ∧
  f.outsideAeon = true ∧
  f.outsideTime = true

/-- Positive predicates become legitimate only after the capture surfaces are
closed. The passage is not "nothing can be said"; it is "first prevent false
capture, then name overflow." -/
structure OverflowAfterRefusal where
  lifeGiving : Bool
  knowledgeGiving : Bool
  goodnessGiving : Bool
  mercyGiving : Bool
  redemptionGiving : Bool
  graceGiving : Bool
deriving DecidableEq, Repr

def monadOverflow : OverflowAfterRefusal where
  lifeGiving := true
  knowledgeGiving := true
  goodnessGiving := true
  mercyGiving := true
  redemptionGiving := true
  graceGiving := true

def givesWithoutCapture (o : OverflowAfterRefusal) : Prop :=
  o.lifeGiving = true ∧
  o.knowledgeGiving = true ∧
  o.goodnessGiving = true ∧
  o.mercyGiving = true ∧
  o.redemptionGiving = true ∧
  o.graceGiving = true

theorem opening_trace_has_anti_idol_order :
    openingTrace.length = 5
    ∧ openingTrace.head? = some OpeningPhase.institutionalWound
    ∧ openingTrace.getLast? = some OpeningPhase.overflowAfterNegation := by
  exact ⟨rfl, rfl, rfl⟩

theorem revealer_is_three_face_non_plural :
    threeFacesOneSource apocryphonThreeFace := by
  unfold threeFacesOneSource apocryphonThreeFace
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem monad_firewall_refuses_capture :
    refusesCapture monadFirewall := by
  unfold refusesCapture monadFirewall
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem monad_overflow_after_refusal :
    givesWithoutCapture monadOverflow := by
  unfold givesWithoutCapture monadOverflow
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The local three-form reading is compatible with the existing triptych braid:
three positions do not force plural source because the full cycle sums to
truth/zero. -/
theorem three_forms_balance_at_truth :
    Gnosis.GnosisTriptychBraid.cycleSum = 0 :=
  Gnosis.GnosisTriptychBraid.cycle_sum_zero

/-- The passage's Monad claim reuses the existing grammar theorem: a monad is
irreducible, not a class-member with a genus and species. -/
theorem apocryphon_monad_reuses_irreducible_monad :
    MonadDyadTriad.MonadStructure.ropelength = 1 ∧
    MonadDyadTriad.MonadStructure.fold = 1 :=
  MonadDyadTriad.monad_is_irreducible

/-- The three-form light is a witness surface in the existing grammar sense:
three elements make the first complete witness cycle. -/
theorem three_form_light_reuses_triad_witness :
    ∃ (a b c : Nat),
      a = 5 ∧ b = 7 ∧ c = 5 ∧
      a + b + c = MonadDyadTriad.TriadStructure.ropelength ∧
      MonadDyadTriad.TriadStructure.fold = 3 :=
  MonadDyadTriad.triad_is_first_witness

/-- Master witness: the Apocryphon opener is an anti-idol compiler. It routes
institutional accusation into desert observation, presents a three-face but
non-plural light-form, refuses every premature category capture, then permits
positive overflow. Existing gnosis-math supplies the formal shape: irreducible
Monad, triadic witness, and sum-zero triptych balance. -/
theorem apocryphon_opening_monad_anti_idol_witness :
    openingTrace.length = 5
    ∧ threeFacesOneSource apocryphonThreeFace
    ∧ refusesCapture monadFirewall
    ∧ givesWithoutCapture monadOverflow
    ∧ Gnosis.GnosisTriptychBraid.cycleSum = 0
    ∧ (MonadDyadTriad.MonadStructure.ropelength = 1 ∧
       MonadDyadTriad.MonadStructure.fold = 1)
    ∧ (∃ (a b c : Nat),
        a = 5 ∧ b = 7 ∧ c = 5 ∧
        a + b + c = MonadDyadTriad.TriadStructure.ropelength ∧
        MonadDyadTriad.TriadStructure.fold = 3) := by
  exact ⟨opening_trace_has_anti_idol_order.1,
    revealer_is_three_face_non_plural,
    monad_firewall_refuses_capture,
    monad_overflow_after_refusal,
    three_forms_balance_at_truth,
    apocryphon_monad_reuses_irreducible_monad,
    three_form_light_reuses_triad_witness⟩

end ApocryphonJohnOpeningMonadWitness
end Gnosis.Witnesses.Gnostic
