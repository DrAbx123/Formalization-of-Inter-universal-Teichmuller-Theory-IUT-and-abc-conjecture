/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618ProofQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightWeightFromTripleQpilotActual
import tmp.sheaf.xif.paper.Mzk1GapShapeAuditQpilotActual
import tmp.sheaf.xif.paper.Mzk1RegionNecessitySummaryQpilotActual
import tmp.sheaf.xif.paper.Mzk1FullAuditSummaryQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual

/-! # Mzk1ThinReexportBundleQpilotActual — thin re-export bundle (A645)

One thin bundle re-exporting the green qpilot results: A618 height/volume
estimates, triple-comparison height-weight bound, gap shapes, region necessity
payload and the full audit summary. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThinReexportBundleQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1FullAuditSummaryQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The thin re-export bundle. -/
structure ThinReexportBundle where
  gapShape : ∀ {X : Type u} {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon),
    Gap1Shape W C.logShellPoint epsilon ∧ Gap2Shape W C.logShellPoint epsilon
  tripleBound : ∀ (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point), HeightWeightBoundShape
  regionNecessity : Nonempty RegionNecessityPayload.{0}
  audit : Nonempty (FullAuditSummary T)

/-- The constructed thin re-export bundle. -/
noncomputable def thinReexportBundle : ThinReexportBundle T where
  gapShape := fun {X} {W} {epsilon} C => gapShapes_iff_comparison C
  tripleBound := fun point C => heightWeightBoundShape_of_tripleComparison T point C
  regionNecessity := ⟨regionNecessityPayload⟩
  audit := ⟨fullAuditSummary T⟩

#check thinReexportBundle

end LeanFormal.IUT.XiFPaper.Mzk1ThinReexportBundleQpilotActual
end
