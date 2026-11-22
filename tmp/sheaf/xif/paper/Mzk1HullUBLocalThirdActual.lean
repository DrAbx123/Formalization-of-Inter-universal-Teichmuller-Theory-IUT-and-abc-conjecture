/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingHaarActual
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-! # A6: strict hull radius (first step toward 1/3 local bound) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBLocalThirdActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingHaarActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
theorem rootImageRadius_lt_one :
    (PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real) < 1 := by
  rw [Mzk1RootImageRadiusFormulaActual.rootImageRadius_eq_p_rpow_reexport]
  have hp : (1 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  have hc : 0 < qVFamNormalizedCoefficient T b :=
    qVFamNormalizedCoefficient_pos (T := T) b
  have hl : 0 < (2 * (l.value : Real)) := by
    have hlpos : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    positivity
  have hpos : 0 < qVFamNormalizedCoefficient T b / (2 * (l.value : Real)) :=
    div_pos hc hl
  rw [show -(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)) =
      -(qVFamNormalizedCoefficient T b / (2 * (l.value : Real))) by ring]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_lt_zero.mpr hpos)
theorem rootImageRadius_lt_unitBallRadius :
    (PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real) < 1 :=
  rootImageRadius_lt_one T b
end LeanFormal.IUT.XiFPaper.Mzk1HullUBLocalThirdActual
end
