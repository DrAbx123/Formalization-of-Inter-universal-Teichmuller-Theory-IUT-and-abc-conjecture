import tmp.sheaf.xif.paper.Mzk1A618AuditProofsShaActual
import tmp.sheaf.xif.paper.Mzk1S1902ComparisonRegionMinimalShaActual
import tmp.sheaf.xif.paper.Mzk1TripleDependentRegionAlignShaActual
import tmp.sheaf.xif.paper.Mzk1CanonicalReexportShaActual

/-!
# shehdd A626 A618/comparison-region summary audit (Sha)

One-place summary audit of the green A618 proof surface, the minimal stable
comparison region, the canonical re-export, and the triple-dependent region
alignment.  All fields are thin re-exports/aliases of green declarations.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1A626SummaryAuditShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A618AuditProofsShaActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionMinimalShaActual
open LeanFormal.IUT.XiFPaper.Mzk1TripleDependentRegionAlignShaActual

theorem summary_audit_rows_length :
    LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual.auditRows.length = 13 :=
  audit_length_proof

theorem summary_gap1_present :
    LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual.auditRows.any
      (fun r => r.name = "Gap1 height estimate") = true :=
  audit_gap1_present

theorem summary_gap2_present :
    LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual.auditRows.any
      (fun r => r.name = "Gap2 volume estimate") = true :=
  audit_gap2_present

theorem summary_triple_scaling_present :
    LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual.auditRows.any
      (fun r => r.name = "triple-dependent scaling design") = true :=
  audit_triple_scaling_present

end LeanFormal.IUT.XiFPaper.Mzk1A626SummaryAuditShaActual

/-! ### Axiom gate: canonical bridge / triple-dependent ABC (read-only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual.s1902Bridge_abc
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
