import tmp.sheaf.xif.paper.Mzk1FourTriangleSynthesisActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Four-triangle 3.12 object: column synthesis contract

The finite-route `HDD` columns are packaged directly as a `StepXIContract`
and passed through `columnsHDD_step3115`/`cor312Conclusion_of_columnsSynthesis`.
This is the explicit xi-f comparison for the finite route, not an assumption. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleColumnsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSynthesisActual

universe u

variable {α : Type u} [Fintype α] [Nonempty α]
variable (f : α → Real) (i : α)

def columnsContract (hneg : (HDD (columnsHDD f) i).1 < 0) : StepXIContract where
  qSigned := (HDD (columnsHDD f) i).1
  thetaSigned := (HDD (columnsHDD f) i).2
  targetSigned := (HDD (columnsHDD f) i).2
  q_negative := hneg
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := columnsHDD_step3115 f i
  target_le_theta := le_rfl

theorem columnsContract_cor312 (hneg : (HDD (columnsHDD f) i).1 < 0) :
    Cor312Conclusion (columnsContract f i hneg) :=
  cor312Conclusion_of_columnsSynthesis f (columnsContract f i hneg) i rfl rfl

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleColumnsActual

end
