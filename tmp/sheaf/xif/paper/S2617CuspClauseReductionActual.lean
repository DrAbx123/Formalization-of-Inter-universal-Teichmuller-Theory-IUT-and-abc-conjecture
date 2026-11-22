import tmp.sheaf.xif.paper.S2616CuspAssemblyActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual
open LeanFormal.IUT.XiFPaper.S1636SourceClausesActual
open LeanFormal.IUT.XiFPaper.S2616CuspAssemblyActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2617CuspClauseReductionActual

variable {l : PrimeGeFive}
variable {S : SourceSignQuotientData (S1280Arithmetic l)}

/-- Exact residual input of D8: a paper cusp local parameter in the actual
completion at the place above 5.  This is the same object as
`S1428CuspLocalParameterRequired`, named at the D8 clause boundary. -/
def S2617CuspClauseInput (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  Nonempty (S1428CuspLocalParameter l S)

theorem S2617CuspClauseInput_iff_required :
    S2617CuspClauseInput l S ↔ S1428CuspLocalParameterRequired l S :=
  Iff.rfl

/-- The D8 real cusp clause from the exact residual input.  This is the
non-conditional consumer of `S2616CuspClause`: only the precise missing
local-parameter datum is assumed, and every field is the actual S1428
valuation object. -/
noncomputable def S2617CuspClauseOfInput
    (h : S2617CuspClauseInput l S) (c : S1330PaperCusp l S) :
    SourceCuspClause :=
  S2616CuspClause (S := S) (P := Classical.choice h) c

theorem S2617CuspClauseOfInput_epsilon
    (h : S2617CuspClauseInput l S) (c : S1330PaperCusp l S) :
    (S2617CuspClauseOfInput h c).epsilon =
      ‖(Classical.choice h).localParameter c‖ := rfl

theorem S2617CuspClauseOfInput_cuspScale
    (h : S2617CuspClauseInput l S) (c : S1330PaperCusp l S) :
    (S2617CuspClauseOfInput h c).cuspScale =
      (‖(Classical.choice h).localParameter c‖)⁻¹ := rfl

/-- The exact input is exactly the S1428 missing object, not a chosen real. -/
noncomputable def S2617CuspClauseInput_hasLocalParameter
    (h : S2617CuspClauseInput l S) :
    S1428CuspLocalParameter l S :=
  Classical.choice h

#print axioms S2617CuspClauseOfInput_epsilon
#print axioms S2617CuspClauseOfInput_cuspScale

end LeanFormal.IUT.XiFPaper.S2617CuspClauseReductionActual
end
