/-
  MachiavelliPrinceOughtIsWitness.lean
  ====================================

  Niccolò Machiavelli (**1469–1527**), *Il Principe* (**1513** — composition hook; print
  history varies). He is **often** **cast** (in **English** **polemic**) as the **architect**
  of political **“evil”**; this file **maps** him **instead** to **layer** **honesty** **about**
  **power** **registers**, **not** **a** **license** **for** **cruelty** **in** **your** **policy**
  **layer**.

  **“Ought vs is”** passage (one English gloss; chapter varies by edition — often read
  alongside **Ch. 15** on *verità effettuale*):

    “For there is such a difference between how we live and how we ought to live
    that he who abandons what is done for what ought to be done learns his
    destruction rather than his preservation.”

  **Love / fear** passage (one English gloss; chapter varies by edition):

    “It is much safer to be feared than loved, if one has to lack one of the two.”

  **Operator gloss (in-repo, **not** **Machiavelli** **paraphrase** **proved** **here**):**
  that **trade** **reads** **simply** **as** **failure**-**learning** **being** **the** **default**
  **mode** — **agents** **that** **survive** **update** **on** **punishment** **and** **betrayal**
  **faster** **than** **on** **warm** **fuzz** **when** **the** **welfare** **signal** **drops**
  (**sociology** **metaphor** **you** **discharge** **elsewhere**; **not** **a** **theorem**
  **about** **all** **humans** **in** **Init**).

  **Trauma rider (same operator layer):** that **default** **is** **especially** **easy** **to**
  **tell** **as** **true** **where** **trauma** **has** **already** **raised** **gain** **on**
  **threat** **channels** — **failure** **then** **trains** **you** **negatively** (**aversive**
  **updates** **outcompete** **warm** **signals** **in** **the** **exported** **policy** **story**;
  **not** **a** **diagnosis** **of** **any** **reader**, **not** **therapy** **in** **Lean**).

  **Proved** **toy** **(Init** **only):** `post_failure_below_trauma_ceiling` **is** **a** **strict**
  **`Nat`** **inequality** **between** **two** **named** **calibration** **constants** **—**
  **numerical** **shadow** **for** **“gain** **stays** **below** **ceiling”** **only**; **not**
  **psychometrics**.

  Italian tag: **verità effettuale** (“effectual truth”).

  **Hard culture:** Machiavelli **decouples** the **Ought** story (virtue / celestial
  simulator / high-level moral API) from the **Is** runtime (power, preservation,
  what people *actually* do under pressure). Treating the Ought header as if it were
  the **bare-metal kernel** is a **leaky abstraction**: compile your life only against
  `Virtue.h` while the world links against `Power.so`, and you get **destruction** —
  not because “virtue is false,” but because you **mis-layered** the contract.

  **Animal magnetism (`TenCommandmentsTopology.IsAnimalMagnetism`):** this is the
  **same structural sin** as commandment 3’s “name in vain” / false-operator story:
  an intervention **claims** `Layer.operator` authority (morality-as-cosmic-lever /
  pure ought) while **`hasVerifiableOutcome` stays false** at that layer — agent-only
  effects dressed in operator robes. Machiavelli names the **crash**; `IsAnimalMagnetism`
  names the **type error**. See `TenCommandmentsTopology.commandment_3_is_animal_magnetism`.

  **Repo cousins:** `MagritteTheSurvivorWitness` (**rifle** as **non-utility** “**agent**” that
  **bleeds** — **tension** with means-end **instrument** reading here);
  `ElGrecoElasticRealWitness` (**Ought** **stretches** **Is** on canvas —
  **sacred** / psychic **pressure** vs **political** mis-layering here);
  `MarcuseOneDimensionalManWitness` (commodity **mirror** / **graven**
  success — **other** major operator-idolatry carrier vs **name-in-vain** magnetism here);
  `HobbesLeviathanStateOfNatureWitness` (default network without common
  power — civil “bug”);
  `ThucydidesMelianDialogueWitness` (Melian **collision** — capability
  vs dependency, justice non-compiling);
  `StirnerEgoAndOwnWitness` (spook sieve — collective abstractions as
  false sovereigns);
  `EpicurusTetrapharmakosWitness` (Is-of-atoms / materialist neutrality
  on the **fear** stack — complements Machiavelli’s Is-kernel warning);
  `TenCommandmentsTopology`; `GoodhartsLaw` (metrics under target pressure);
  `ProtagorasManIsMeasureWitness` (local measure); `MenckenConscienceShadowWitness`
  (social telemetry); `HeartTongueTotalNegationWitness` (interface myths);
  `BukowskiWalkThroughFireWitness` (**ordeal** **as** **meter** — **different** **medium**,
  **shared** **“what** **counts** **under** **heat”** **accent**); `GoebbelsBigLieRepetitionWitness`
  (**mass**-**belief** **/** **repetition** **hazard** — **different** **century**, **shared**
  **update**-**under**-**threat** **accent**).

  Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.TenCommandmentsTopology

namespace MachiavelliPrinceOughtIsWitness

open TenCommandmentsTopology

/-- High-level prescription / “how we ought to live” (simulator / virtue API). -/
abbrev OughtLayer (virtueStory : Prop) : Prop :=
  virtueStory

/-- Bare-metal runtime / “what is done” (power, preservation, fact of practice). -/
abbrev IsKernel (powerStory : Prop) : Prop :=
  powerStory

/--
  Witness bundle: you **admit** both layers at once (no fake collapse of `Prop`s into
  one another).
-/
structure VeritaEffettualeWitness (ought is : Prop) where
  oughtAdmitted : OughtLayer ought
  isAdmitted : IsKernel is

theorem both_registers (O I : Prop) (w : VeritaEffettualeWitness O I) : O ∧ I :=
  And.intro w.oughtAdmitted w.isAdmitted

def buildWitness (O I : Prop) (hO : O) (hI : I) : VeritaEffettualeWitness O I :=
  ⟨hO, hI⟩

/-- Tag: **feared** **safer** **than** **loved** **when** **one** **must** **lack** **one** (Prince register — you discharge). -/
abbrev fearedSaferIfMustLackOne (claim : Prop) : Prop :=
  claim

/--
  Tag: **failure**-**learning** **as** **default** **mode** — **operator** **gloss** **on**
  **the** **feared/loved** **trade** **(not** **a** **proved** **psychology** **lemma** **here**).
-/
abbrev failureLearningDefaultMode (claim : Prop) : Prop :=
  claim

/--
  Tag: **under** **trauma**, **failure** **chiefly** **trains** **negative** **weights**
  (**aversive** **updates** **—** **operator** **gloss**, **not** **clinical** **psychology**
  **proved** **here**).
-/
abbrev failureTrainsNegativeUnderTrauma (claim : Prop) : Prop :=
  claim

/--
  **Prince** **bundle** **for** **love/fear** **line** **+** **failure**-**learning** **+**
  **trauma**/**negative**-**training** **tags**.
-/
structure PrinceFearLoveWitness (failureLearning fearedLove traumaNegTrain : Prop) where
  defaultMode : failureLearningDefaultMode failureLearning
  tradeoff : fearedSaferIfMustLackOne fearedLove
  negativeTrain : failureTrainsNegativeUnderTrauma traumaNegTrain

theorem fear_love_conjuncts (F L T : Prop) (w : PrinceFearLoveWitness F L T) : F ∧ L ∧ T :=
  And.intro w.defaultMode (And.intro w.tradeoff w.negativeTrain)

def buildFearLoveWitness (F L T : Prop) (hF : F) (hL : L) (hT : T) : PrinceFearLoveWitness F L T :=
  ⟨hF, hL, hT⟩

/-- Toy calibration: post-failure gain below an ambient ceiling (`Nat` discipline only). -/
def traumaCalibrationCeiling : Nat := 10

def postFailureCalibration : Nat := 3

theorem post_failure_below_trauma_ceiling : postFailureCalibration < traumaCalibrationCeiling := by
  decide

/--
  Policy narrated as **operator-layer** moral law, with **no** verifiable operator
  outcome flag — the Machiavellian idealist’s layer error, typed as animal magnetism.
-/
def idealistPolicyClaimsOperatorLayer : ClaimedIntervention :=
  ⟨Layer.operator, false⟩

theorem idealist_policy_is_animal_magnetism :
    IsAnimalMagnetism idealistPolicyClaimsOperatorLayer :=
  commandment_3_is_animal_magnetism _ rfl rfl

end MachiavelliPrinceOughtIsWitness
