/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1AcceptanceFinalRewriteActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureSignedConsumerActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual

/-! # Mzk1AcceptanceWrapUpActual — acceptance wrap-up over green components (A572)

Green-only wrap-up: paper target equivalence, half-ball qRegion normalized volume,
and their conjunction as the acceptance summary. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AcceptanceWrapUpActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalRewriteActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureSignedConsumerActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem wrapup_paperTarget_iff (qMag thetaMag : Real) :
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag :=
  acceptance_paperTarget_iff qMag thetaMag

theorem wrapup_qRegion_normalized :
    qNormalizedVolume T (qRegion T) = 1 :=
  qNormalizedVolume_qRegion_eq T

theorem wrapup_summary :
    (∀ qMag thetaMag : Real, paperTarget qMag thetaMag ↔ thetaMag ≤ qMag) ∧
      qNormalizedVolume T (qRegion T) = 1 :=
  ⟨wrapup_paperTarget_iff, wrapup_qRegion_normalized T⟩

#check wrapup_summary

end LeanFormal.IUT.XiFPaper.Mzk1AcceptanceWrapUpActual
end
