import Init

/-!
# Syllogistic Logic

Init-only formalization of the 24 traditionally valid categorical syllogisms.
The unconditional forms prove directly under modern first-order semantics.
The conditional forms make their existential import explicit as a premise on
the required term.
-/

namespace Gnosis.GreekLogicCanon.SyllogisticLogic

universe u

inductive CategoricalCode where
  | A
  | E
  | I
  | O
deriving DecidableEq, Repr

inductive Figure where
  | first
  | second
  | third
  | fourth
deriving DecidableEq, Repr

inductive ValidityKind where
  | unconditional
  | conditional
deriving DecidableEq, Repr

inductive ExistentialImport where
  | minorTerm
  | middleTerm
  | majorTerm
deriving DecidableEq, Repr

structure SyllogismSignature where
  name : String
  aliases : List String
  major : CategoricalCode
  minor : CategoricalCode
  conclusion : CategoricalCode
  figure : Figure
  validity : ValidityKind
  requiredImport : Option ExistentialImport
deriving Repr

def mkUnconditional
    (name : String)
    (aliases : List String)
    (major minor conclusion : CategoricalCode)
    (figure : Figure) : SyllogismSignature where
  name := name
  aliases := aliases
  major := major
  minor := minor
  conclusion := conclusion
  figure := figure
  validity := .unconditional
  requiredImport := none

def mkConditional
    (name : String)
    (aliases : List String)
    (major minor conclusion : CategoricalCode)
    (figure : Figure)
    (requiredImport : ExistentialImport) : SyllogismSignature where
  name := name
  aliases := aliases
  major := major
  minor := minor
  conclusion := conclusion
  figure := figure
  validity := .conditional
  requiredImport := some requiredImport

def unconditionallyValidSyllogisms : List SyllogismSignature :=
  [ mkUnconditional "Barbara" [] .A .A .A .first
  , mkUnconditional "Celarent" [] .E .A .E .first
  , mkUnconditional "Darii" [] .A .I .I .first
  , mkUnconditional "Ferio" [] .E .I .O .first
  , mkUnconditional "Cesare" [] .E .A .E .second
  , mkUnconditional "Camestres" [] .A .E .E .second
  , mkUnconditional "Festino" [] .E .I .O .second
  , mkUnconditional "Baroco" [] .A .O .O .second
  , mkUnconditional "Disamis" [] .I .A .I .third
  , mkUnconditional "Datisi" [] .A .I .I .third
  , mkUnconditional "Bocardo" [] .O .A .O .third
  , mkUnconditional "Ferison" [] .E .I .O .third
  , mkUnconditional "Camenes" ["Calemes"] .A .E .E .fourth
  , mkUnconditional "Dimaris" ["Dimatis"] .I .A .I .fourth
  , mkUnconditional "Fresison" [] .E .I .O .fourth
  ]

def conditionallyValidSyllogisms : List SyllogismSignature :=
  [ mkConditional "Barbari" [] .A .A .I .first .minorTerm
  , mkConditional "Celaront" [] .E .A .O .first .minorTerm
  , mkConditional "Cesaro" [] .E .A .O .second .minorTerm
  , mkConditional "Camestrop" ["Camestros"] .A .E .O .second .minorTerm
  , mkConditional "Darapti" [] .A .A .I .third .middleTerm
  , mkConditional "Felapton" [] .E .A .O .third .middleTerm
  , mkConditional "Bramantip" ["Bamalip"] .A .A .I .fourth .majorTerm
  , mkConditional "Camenop" ["Calemos"] .A .E .O .fourth .minorTerm
  , mkConditional "Fesapo" [] .E .A .O .fourth .middleTerm
  ]

def validSyllogisms : List SyllogismSignature :=
  unconditionallyValidSyllogisms ++ conditionallyValidSyllogisms

def validSyllogismCatalogSize : Nat :=
  validSyllogisms.length

abbrev Term (α : Type u) := α -> Prop

abbrev A {α : Type u} (subject predicate : Term α) : Prop :=
  ∀ x, subject x -> predicate x

abbrev E {α : Type u} (subject predicate : Term α) : Prop :=
  ∀ x, subject x -> ¬ predicate x

abbrev I {α : Type u} (subject predicate : Term α) : Prop :=
  ∃ x, subject x ∧ predicate x

abbrev O {α : Type u} (subject predicate : Term α) : Prop :=
  ∃ x, subject x ∧ ¬ predicate x

abbrev ExistsTerm {α : Type u} (term : Term α) : Prop :=
  ∃ x, term x

theorem barbara_AAA_1 {α : Type u} {S M P : Term α}
    (major : A M P)
    (minor : A S M) :
    A S P := by
  intro x hxS
  exact major x (minor x hxS)

theorem celarent_EAE_1 {α : Type u} {S M P : Term α}
    (major : E M P)
    (minor : A S M) :
    E S P := by
  intro x hxS
  exact major x (minor x hxS)

theorem darii_AII_1 {α : Type u} {S M P : Term α}
    (major : A M P)
    (minor : I S M) :
    I S P := by
  cases minor with
  | intro x hx =>
      exact Exists.intro x (And.intro hx.left (major x hx.right))

theorem ferio_EIO_1 {α : Type u} {S M P : Term α}
    (major : E M P)
    (minor : I S M) :
    O S P := by
  cases minor with
  | intro x hx =>
      exact Exists.intro x (And.intro hx.left (major x hx.right))

theorem barbari_AAI_1 {α : Type u} {S M P : Term α}
    (major : A M P)
    (minor : A S M)
    (minorExists : ExistsTerm S) :
    I S P := by
  cases minorExists with
  | intro x hxS =>
      exact Exists.intro x (And.intro hxS (major x (minor x hxS)))

theorem celaront_EAO_1 {α : Type u} {S M P : Term α}
    (major : E M P)
    (minor : A S M)
    (minorExists : ExistsTerm S) :
    O S P := by
  cases minorExists with
  | intro x hxS =>
      exact Exists.intro x (And.intro hxS (major x (minor x hxS)))

theorem cesare_EAE_2 {α : Type u} {S M P : Term α}
    (major : E P M)
    (minor : A S M) :
    E S P := by
  intro x hxS
  intro hxP
  exact major x hxP (minor x hxS)

theorem camestres_AEE_2 {α : Type u} {S M P : Term α}
    (major : A P M)
    (minor : E S M) :
    E S P := by
  intro x hxS
  intro hxP
  exact minor x hxS (major x hxP)

theorem festino_EIO_2 {α : Type u} {S M P : Term α}
    (major : E P M)
    (minor : I S M) :
    O S P := by
  cases minor with
  | intro x hx =>
      exact
        Exists.intro x
          (And.intro hx.left (fun hxP => major x hxP hx.right))

theorem baroco_AOO_2 {α : Type u} {S M P : Term α}
    (major : A P M)
    (minor : O S M) :
    O S P := by
  cases minor with
  | intro x hx =>
      exact
        Exists.intro x
          (And.intro hx.left (fun hxP => hx.right (major x hxP)))

theorem cesaro_EAO_2 {α : Type u} {S M P : Term α}
    (major : E P M)
    (minor : A S M)
    (minorExists : ExistsTerm S) :
    O S P := by
  cases minorExists with
  | intro x hxS =>
      exact
        Exists.intro x
          (And.intro hxS (fun hxP => major x hxP (minor x hxS)))

theorem camestrop_AEO_2 {α : Type u} {S M P : Term α}
    (major : A P M)
    (minor : E S M)
    (minorExists : ExistsTerm S) :
    O S P := by
  cases minorExists with
  | intro x hxS =>
      exact
        Exists.intro x
          (And.intro hxS (fun hxP => minor x hxS (major x hxP)))

theorem disamis_IAI_3 {α : Type u} {S M P : Term α}
    (major : I M P)
    (minor : A M S) :
    I S P := by
  cases major with
  | intro x hx =>
      exact Exists.intro x (And.intro (minor x hx.left) hx.right)

theorem datisi_AII_3 {α : Type u} {S M P : Term α}
    (major : A M P)
    (minor : I M S) :
    I S P := by
  cases minor with
  | intro x hx =>
      exact Exists.intro x (And.intro hx.right (major x hx.left))

theorem bocardo_OAO_3 {α : Type u} {S M P : Term α}
    (major : O M P)
    (minor : A M S) :
    O S P := by
  cases major with
  | intro x hx =>
      exact Exists.intro x (And.intro (minor x hx.left) hx.right)

theorem ferison_EIO_3 {α : Type u} {S M P : Term α}
    (major : E M P)
    (minor : I M S) :
    O S P := by
  cases minor with
  | intro x hx =>
      exact Exists.intro x (And.intro hx.right (major x hx.left))

theorem darapti_AAI_3 {α : Type u} {S M P : Term α}
    (major : A M P)
    (minor : A M S)
    (middleExists : ExistsTerm M) :
    I S P := by
  cases middleExists with
  | intro x hxM =>
      exact Exists.intro x (And.intro (minor x hxM) (major x hxM))

theorem felapton_EAO_3 {α : Type u} {S M P : Term α}
    (major : E M P)
    (minor : A M S)
    (middleExists : ExistsTerm M) :
    O S P := by
  cases middleExists with
  | intro x hxM =>
      exact Exists.intro x (And.intro (minor x hxM) (major x hxM))

theorem camenes_AEE_4 {α : Type u} {S M P : Term α}
    (major : A P M)
    (minor : E M S) :
    E S P := by
  intro x hxS
  intro hxP
  exact minor x (major x hxP) hxS

theorem dimaris_IAI_4 {α : Type u} {S M P : Term α}
    (major : I P M)
    (minor : A M S) :
    I S P := by
  cases major with
  | intro x hx =>
      exact Exists.intro x (And.intro (minor x hx.right) hx.left)

theorem fresison_EIO_4 {α : Type u} {S M P : Term α}
    (major : E P M)
    (minor : I M S) :
    O S P := by
  cases minor with
  | intro x hx =>
      exact
        Exists.intro x
          (And.intro hx.right (fun hxP => major x hxP hx.left))

theorem bramantip_AAI_4 {α : Type u} {S M P : Term α}
    (major : A P M)
    (minor : A M S)
    (majorExists : ExistsTerm P) :
    I S P := by
  cases majorExists with
  | intro x hxP =>
      exact
        Exists.intro x
          (And.intro (minor x (major x hxP)) hxP)

theorem camenop_AEO_4 {α : Type u} {S M P : Term α}
    (major : A P M)
    (minor : E M S)
    (minorExists : ExistsTerm S) :
    O S P := by
  cases minorExists with
  | intro x hxS =>
      exact
        Exists.intro x
          (And.intro hxS (fun hxP => minor x (major x hxP) hxS))

theorem fesapo_EAO_4 {α : Type u} {S M P : Term α}
    (major : E P M)
    (minor : A M S)
    (middleExists : ExistsTerm M) :
    O S P := by
  cases middleExists with
  | intro x hxM =>
      exact
        Exists.intro x
          (And.intro (minor x hxM) (fun hxP => major x hxP hxM))

end Gnosis.GreekLogicCanon.SyllogisticLogic
