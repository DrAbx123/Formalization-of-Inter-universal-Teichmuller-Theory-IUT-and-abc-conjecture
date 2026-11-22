/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperToClassicalABCActual
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import Mathlib.Tactic

/-! # A973: IUT line modulo ONE inequality (single-sorry architecture) -

THIS FILE CONTAINS THE UNIQUE ALLOWED `sorry` OF THE IUT LINE: `ssIneq_sorry`.
Its statement is the paper 3.12 inequality `Paper312Statement C3 P`
(`qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3`); every other ingredient is
proved in green files or is an EXPLICIT class-B external assumption (`ClassBEdge`, the
missing edge `Cor312Conclusion/paperGap -> ClassicalABCShape`, registered from
`Mzk1PaperToClassicalABCActual.edgeRows`).  No axiom is declared. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTModuloInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperToClassicalABCActual
open LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCToOurABCActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The paper 3.12 inequality surface for the single sorry. -/
def PaperInequality : Prop := Paper312Statement C3 P

/-- **THE UNIQUE `sorry`**: the paper 3.12 inequality (S3137 readings comparison). -/
theorem ssIneq_sorry : PaperInequality C3 P := by
  sorry

/-- Class-B external edge (registered missing edge): paper inequality -> `ClassicalABCShape`.
Stated as an explicit assumption field, NOT an axiom. -/
structure ClassBEdge where
  edge : PaperInequality C3 P → ClassicalABCShape

/-- Green step: the paper inequality (from the unique sorry) plus the class-B edge give
`ClassicalABCShape`. -/
theorem classicalABCShape_of_sorry (E : ClassBEdge C3 P) : ClassicalABCShape :=
  E.edge (ssIneq_sorry C3 P)

/-- Green step: `ClassicalABCShape -> ABCConjecture` (proved in the paper bridge file). -/
theorem ABCFinal (E : ClassBEdge C3 P) : ABCConjecture :=
  classicalABCShape_to_ABCConjecture (classicalABCShape_of_sorry C3 P E)

def singleSorryRows : List (String × String) :=
  [ ("ssIneq_sorry", "UNIQUE sorry: Paper312Statement C3 P") ,
    ("ClassBEdge", "external edge paper inequality -> ClassicalABCShape (registered)") ,
    ("classicalABCShape_of_sorry", "green composition") ,
    ("ABCFinal", "green: ClassicalABCShape -> ABCConjecture") ]

theorem singleSorryRows_length : singleSorryRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1IUTModuloInequalityActual
