import tmp.sheaf.xif.paper.Mzk1FinalBoundaryShaActual
import tmp.sheaf.xif.paper.Mzk1A618MachineProofThinShaActual
import tmp.sheaf.xif.paper.Mzk1GapTightnessShaActual

/-!
# shehdd A649 FinalBoundary certificate (Sha, read-only conjunction)

Single-conjunction boundary certificate built ONLY from green shehdd files:
(a) the boundary table has 9 rows;
(b) Gap 1 and Gap 2 rows are present and stay NAMED;
(c) the ABC gate row is CONDITIONAL (gaps are explicit hypotheses);
(d) the green A618 machine obstruction is re-exported (thin, gate trio);
(e) scope: boundary certificate only; ABC NOT proved.

This is the shehdd Sha counterpart of the mainline `Mzk1FinalBoundaryCertificateActual`
(currently red; diagnosed separately).  No mainline file is changed.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateShaActual

open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryShaActual
open LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofThinShaActual

/-- The shehdd final boundary certificate as one conjunction. -/
theorem finalBoundaryCertificateSha :
    boundaryRows.length = 9 ∧
      boundaryRows.any (fun r => r.component = "Gap 1") = true ∧
      boundaryRows.any (fun r => r.component = "Gap 2") = true ∧
      boundaryRows.any (fun r => r.status = "CONDITIONAL") = true :=
  ⟨boundaryRows_length, boundary_has_gap1, boundary_has_gap2,
    boundary_has_conditional_gate⟩

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateShaActual

/-! ### Axiom gates (read-only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateShaActual.finalBoundaryCertificateSha
#print axioms LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofThinShaActual.a618_machine_obstruction_thin
