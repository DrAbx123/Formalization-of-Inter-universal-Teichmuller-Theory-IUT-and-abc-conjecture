import tmp.sheaf.xif.paper.Mzk1FourTriangleSynthesisActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Four-triangle 3.12 object: finite-route columns as (HDD)∘(dsc)∘(SHE)

Uses the green `Mzk1FourTriangleSynthesisActual` objects `columnsHDD` and
`cor312Conclusion_of_fourTriangleSynthesis` to build a concrete finite-route
`FourTriangleSynthesis`; the xi-f comparison is the actual columnwise
`columnsHDD_step3115`, not a Prop placeholder. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleFiniteRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSynthesisActual

universe u

variable {α : Type u} [Fintype α] [Nonempty α]
variable (f : α → Real) (i : α)

def finiteRouteContract (hneg : (HDD (columnsHDD f) i).1 < 0) : StepXIContract where
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

def finiteRouteSynthesis (hneg : (HDD (columnsHDD f) i).1 < 0) :
    FourTriangleSynthesis α α where
  contract := finiteRouteContract f i hneg
  hdd := columnsHDD f
  dsc := id
  sheOut := i
  hull_eq := rfl
  theta_eq := rfl
  step3115_comparison := columnsHDD_step3115 f i

theorem finiteRoute_cor312 (hneg : (HDD (columnsHDD f) i).1 < 0) :
    Cor312Conclusion (finiteRouteContract f i hneg) :=
  cor312Conclusion_of_fourTriangleSynthesis (finiteRouteSynthesis f i hneg)

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleFiniteRouteActual

end
