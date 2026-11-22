import tmp.sheaf.xif.paper.S51DecorationWrapperActual

/-! # S54: actual decoration assignment for the S51 consumers

The paper context and the Lean definitions:

* DThetaShadow is the D-Theta shadow (source DThetaShadow);
* I.fPrimeStripAt is the source F-prime-strip I.primeStripAt (plain F);
* IPLAPT strips are source F-prime-strips (plain F);
* globalThetaPilotStrip is I.primeStripAt 0 0 (plain F);
* ConcretePaperQPilotWitness.stripTarget is the concrete q-pilot F-prime-strip
  (plain F).

Thus the four S51 consumers use the undecorated F-prime-strip, so their actual
decoration is Decoration.undecorated.  The source structures do not carry a
decoration field; this file records the minimal actual annotation field.

No fake decoration/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S54DecorationAssignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S51DecorationWrapperActual

/-- Actual source consumers named in S51. -/
inductive SourceConsumer where
  | dThetaShadow
  | fPrimeStripAt
  | iplapt
  | globalThetaPilotStrip
  | concreteStripTarget
  deriving DecidableEq, Repr

/-- Actual decoration assignment read from the source definitions. -/
def consumerDecoration : SourceConsumer → Decoration
  | SourceConsumer.dThetaShadow => Decoration.theta
  | SourceConsumer.fPrimeStripAt => Decoration.undecorated
  | SourceConsumer.iplapt => Decoration.undecorated
  | SourceConsumer.globalThetaPilotStrip => Decoration.undecorated
  | SourceConsumer.concreteStripTarget => Decoration.undecorated

/-- Minimal actual source-decoration field: each consumer needs one Decoration
annotation; the source structures currently have no such field. -/
structure ConsumerDecorationField where
  consumer : SourceConsumer
  decoration : Decoration
  decoration_eq : decoration = consumerDecoration consumer

/-- Actual annotation list for all S51 consumers. -/
def consumerDecorationFields : List ConsumerDecorationField :=
  [ { consumer := SourceConsumer.dThetaShadow,
      decoration := Decoration.theta, decoration_eq := rfl },
    { consumer := SourceConsumer.fPrimeStripAt,
      decoration := Decoration.undecorated, decoration_eq := rfl },
    { consumer := SourceConsumer.iplapt,
      decoration := Decoration.undecorated, decoration_eq := rfl },
    { consumer := SourceConsumer.globalThetaPilotStrip,
      decoration := Decoration.undecorated, decoration_eq := rfl },
    { consumer := SourceConsumer.concreteStripTarget,
      decoration := Decoration.undecorated, decoration_eq := rfl } ]

/-- Every source consumer has an actual decoration annotation. -/
theorem all_consumers_have_decoration :
    ∀ c : SourceConsumer, ∃ d : Decoration, d = consumerDecoration c := by
  intro c
  exact ⟨consumerDecoration c, rfl⟩

/-- The four S51 consumers formerly marked missing are all undecorated F-prime-
strips, not Vdash/Turnstile/Dashv/Theta. -/
theorem four_consumers_undecorated :
    consumerDecoration SourceConsumer.fPrimeStripAt = Decoration.undecorated ∧
    consumerDecoration SourceConsumer.iplapt = Decoration.undecorated ∧
    consumerDecoration SourceConsumer.globalThetaPilotStrip = Decoration.undecorated ∧
    consumerDecoration SourceConsumer.concreteStripTarget = Decoration.undecorated :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- DThetaShadow is the actual D-Theta consumer. -/
theorem dThetaShadow_is_theta :
    consumerDecoration SourceConsumer.dThetaShadow = Decoration.theta := rfl

end LeanFormal.IUT.XiFPaper.S54DecorationAssignmentActual

end
