import tmp.sheaf.xif.paper.S2834CompletionAutoTorsionActual
import tmp.sheaf.xif.paper.S2834KernelFieldIdentificationActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S2834InputAuditActual

/-- hV reduces to matching the canonical `S2786VmodBad`; once an `S` is built
with `V_mod_bad = S2786VmodBad`, this is `rfl`. For an arbitrary `S` there is
no automatic proof. -/
theorem S2834_hV_of_VmodBad
    (S : SourceSignQuotientData S2786Arithmetic)
    (h : S.V_mod_bad = S2786VmodBad) :
    S.V_mod_bad = S2786PlaceSelection.V_mod_bad := by
  rw [S2786PlaceSelection_V_mod_bad]
  exact h

#print axioms S2834_hV_of_VmodBad
end LeanFormal.IUT.XiFPaper.S2834InputAuditActual
end