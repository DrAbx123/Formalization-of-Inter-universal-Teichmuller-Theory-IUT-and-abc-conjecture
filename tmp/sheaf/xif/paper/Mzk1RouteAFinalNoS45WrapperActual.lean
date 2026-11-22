/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0S45FreeFinalRouteAActual
import tmp.sheaf.xif.paper.Mzk1GenericNormBridgeActual
import Mathlib.Tactic
/-! # Route A final wrapper: paper comparison without S45 equality

This composes the mainline Route A reduction with the conditional norm bridge:
pointwise donor power relations give `1 <= qVFamNormRatio`, hence the paper-normalized
comparison without S45 `qVFamNormRatio = 1`.  The norm bridge remains an explicit
hypothesis. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.Mzk1RouteAFinalNoS45WrapperActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0S45FreeFinalRouteAActual
open LeanFormal.IUT.XiFPaper.Mzk1GenericNormBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Conditional Route A closure: pointwise norm bridge gives ratio >= 1, and
mainline reduction gives the paper-normalized comparison without S45 equality. -/
theorem finalPaperNormalizedComparison_noS45_of_norm_bridge
    (d : Bad (nativePlaceSelection T) → ℕ)
    (hd : ∀ b, 1 ≤ d b)
    (hbridge : ∀ b, qVFamNormalizedNorm T b =
      (qVFamDefaultNorm T b) ^ (1 / (d b : ℝ))) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  finalPaperNormalizedComparison_noS45_of_ratio_ge_one T
    (fun b => qVFamNormRatio_ge_one_of_norm_bridge T b (d b) (hd b) (hbridge b))
def routeAFinalNoS45Rows : List (String × String × String) :=
  [ ("finalPaperNormalizedComparison_noS45_of_norm_bridge", "pointwise norm bridge => paper comparison without S45", "PROVED (conditional on norm bridge)"),
    ("qVFamNormRatio_ge_one_of_norm_bridge", "norm bridge => ratio >= 1", "PROVED (conditional)"),
    ("S45 ratio=1", "only used for strict equality, not for comparison", "NOT USED") ]
theorem routeAFinalNoS45Rows_length : routeAFinalNoS45Rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1RouteAFinalNoS45WrapperActual
end