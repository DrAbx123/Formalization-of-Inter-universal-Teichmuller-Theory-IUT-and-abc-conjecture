import tmp.sheaf.xif.paper.S1636SourceClausesActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual
open LeanFormal.IUT.XiFPaper.S1636SourceClausesActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2616CuspAssemblyActual

variable {l : PrimeGeFive}
variable (S : SourceSignQuotientData (S1280Arithmetic l))
variable (P : S1428CuspLocalParameter l S)
variable (c : S1330PaperCusp l S)

noncomputable def S2616CuspClause : SourceCuspClause :=
  S1636CuspClauseOfLocalParameter l S P c

theorem S2616CuspClause_epsilon :
    (S2616CuspClause S P c).epsilon = ‖P.localParameter c‖ := rfl

theorem S2616CuspClause_cuspScale :
    (S2616CuspClause S P c).cuspScale = (‖P.localParameter c‖)⁻¹ := rfl

theorem S2616CuspClause_epsilon_pos :
    0 < (S2616CuspClause S P c).epsilon :=
  S1636CuspClauseOfLocalParameter_epsilon_pos l S P c

theorem S2616CuspClause_cuspScale_pos :
    0 < (S2616CuspClause S P c).cuspScale :=
  S1636CuspClauseOfLocalParameter_cuspScale_pos l S P c

theorem S2616CuspClause_epsilon_mul_scale :
    (S2616CuspClause S P c).epsilon *
      (S2616CuspClause S P c).cuspScale = 1 :=
  S1636CuspClauseOfLocalParameter_epsilon_mul_scale l S P c

def S2616CuspLocalParameterMissing : Prop :=
  Nonempty (S1428CuspLocalParameter l S)

#check S2616CuspClause
#check S2616CuspClause_epsilon
#check S2616CuspClause_cuspScale
#check S2616CuspLocalParameterMissing
#print axioms S2616CuspClause_epsilon_mul_scale

end LeanFormal.IUT.XiFPaper.S2616CuspAssemblyActual
end