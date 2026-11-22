import tmp.sheaf.xif.paper.Mzk1P1StepMaxDegActual
import tmp.sheaf.xif.paper.Mzk1StepProviderGapStatementsActual
import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeAssemblyActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureDecreaseAssemblyActual — P1 lex measure decrease from f4a + numMax gap

Real Lean (no sorry/axiom): the concrete P1 lexicographic measure decrease
(P1MeasureDecreaseInput, consumed by stepProvider'_of_named) follows from
  (i) f4a maxDegP non-increase (PROVED in Mzk1P1StepMaxDegActual), and
  (ii) the named P1 numMax strict statement on the stable-maxDeg branch
       (P1NumMaxStrictStatement, the f4b gap).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureDecreaseAssemblyActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssemblyActual

attribute [local instance] Classical.decEq

universe u

/-- The P1 lex measure decrease follows from f4a (PROVED) and the f4b numMax statement. -/
theorem p1MeasureDecrease_of_f4a_and_numMax
    (hnum : P1NumMaxStrictStatement) : P1MeasureDecreaseInput := by
  intro S alpha0 hgt hdeg
  have hle : maxDegP (stepSetP1 S alpha0) <= maxDegP S :=
    maxDegP_stepSetP1_le S alpha0 hdeg
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hnum S alpha0 hgt hdeg heq⟩

/-- Row record. -/
def p1MeasureDecreaseAssemblyRows : List (String × String) :=
  [ ("p1MeasureDecrease_of_f4a_and_numMax", "PROVED CONDITIONAL (f4a PROVED; f4b named)") ]

theorem p1MeasureDecreaseAssemblyRows_length : p1MeasureDecreaseAssemblyRows.length = 1 := rfl

#check p1MeasureDecrease_of_f4a_and_numMax

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureDecreaseAssemblyActual
end
