import tmp.sheaf.xif.paper.Mzk1StepProviderGapStatementsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! Mainline: reuse chain for StepProvider gap statement layer (re-exports). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapReuseActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual

universe u

theorem p1NumMaxStrictStatement_iff :
    P1NumMaxStrictStatement ↔
      ∀ (S : Finset (P1Point Qbar)) (alpha0 : Qbar),
        1 < maxDegP S → degQ alpha0 = maxDegP S →
          maxDegP (stepSetP1 S alpha0) = maxDegP S →
            numMaxP (stepSetP1 S alpha0) < numMaxP S :=
  Iff.rfl

theorem fixedBetaChoice_reuse :
    FixedBetaChoiceStatement ↔ StepProviderFixedBetaChoiceInput :=
  fixedBetaChoice_iff

theorem gapStatementsRows_length_reuse : gapStatementsRows.length = 2 :=
  gapStatementsRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapReuseActual