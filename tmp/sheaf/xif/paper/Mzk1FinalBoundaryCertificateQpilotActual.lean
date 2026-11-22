/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalCertificateQpilotActual
import tmp.sheaf.xif.paper.Mzk1FinalBoundaryQpilotActual
import Mathlib.Tactic

/-! # Mzk1FinalBoundaryCertificateQpilotActual — final boundary certificate (A650)

Combines the final certificate (cor312 payload, gate rows, strictness, gap witness)
with the boundary payload (hqneg discharge, triple height-weight bound, region
necessity) into one certificate object. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalCertificateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The final boundary certificate. -/
structure FinalBoundaryCertificate where
  certificate : FinalCertificate T
  payload : FinalBoundaryPayload T
  boundaryRows : finalBoundaryRows.length = 6

/-- The constructed final boundary certificate. -/
noncomputable def finalBoundaryCertificate : FinalBoundaryCertificate T where
  certificate := finalCertificate T
  payload := finalBoundaryPayload T
  boundaryRows := finalBoundaryRows_length

#check finalBoundaryCertificate

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateQpilotActual
end
