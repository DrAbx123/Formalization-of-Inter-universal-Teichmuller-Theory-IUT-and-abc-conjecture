import tmp.sheaf.xif.paper.Mzk1P1StepMaxDegActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepMaxDegConsumerActual — consumer of f4a: existence of a step with bounded degree

Real Lean (no sorry/axiom): combining the PROVED max-degree selection (f1) with the f4a
max-degree non-increase, for every finite P1 set S with maxDegP S > 1 there is a selected
alpha0 in S at maximal degree whose concrete f0 step target has P1 maximal degree bounded
by maxDegP S.  This is the paper's "one can choose the step so that degrees do not grow"
statement for the Problem C nested induction.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegActual

attribute [local instance] Classical.decEq

universe u

/-- Existence of a maximal-degree step with bounded P1 degree; note alpha0 is selected in S
(f1 PROVED), and f4a gives the bound. -/
theorem exists_maxDegP_stepSetP1_le (S : Finset (P1Point Qbar)) (hgt : 1 < maxDegP S) :
    exists (alpha0 : Qbar), P1Point.ofFinite alpha0 ∈ S ∧ degQ alpha0 = maxDegP S ∧
      maxDegP (stepSetP1 S alpha0) <= maxDegP S := by
  obtain ⟨alpha0, halpha0S, hdeg⟩ := exists_maxDegP_finite S hgt
  exact ⟨alpha0, halpha0S, hdeg, maxDegP_stepSetP1_le S alpha0 hdeg⟩

/-- Row record. -/
def p1StepMaxDegConsumerRows : List (String × String) :=
  [ ("exists_maxDegP_stepSetP1_le", "PROVED (f1 + f4a)") ]

theorem p1StepMaxDegConsumerRows_length : p1StepMaxDegConsumerRows.length = 1 := rfl

#check exists_maxDegP_stepSetP1_le

end LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegConsumerActual
end
