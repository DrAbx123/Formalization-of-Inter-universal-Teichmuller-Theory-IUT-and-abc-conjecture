/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.BadPlaceNormalizationSourceActual
import Mathlib.Tactic

/-! # A762 hull: log form of `rootImageRadius` (built on green S709)

S709 (`S709RootImageRadiusFormulaActual`, green olean) proves:

* `rootImageRadius_eq_rootNorm : rootImageRadius_b = rootNormedElementNorm_b`;
* `rootImageRadius_eq_p_rpow :
   rootImageRadius_b = p_b ^ (-(c_norm_b)/(2*l))`.

This file records the log form used in the A760/A762 dictionary:

  `log rootImageRadius_b = -(c_norm_b * log p_b)/(2*l)`,

and, when the normalization correction vanishes,

  `log rootImageRadius_b = -((qVFamily T b).order * log p_b)/(2*l)`.

The radius coefficient is therefore `-1/(2l)` in terms of `log p`; the
`sFactor (nC) - 1` coefficient of lana `SSIneq` does NOT come from the radius
but from the procession/label average. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open scoped ENNReal BigOperators NNReal Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Re-export: the hull radius is the root norm. -/
theorem rootImageRadius_eq_rootNorm_reexport :
    (rootImageRadius T b : Real) = rootNormedElementNorm T b :=
  S709RootImageRadiusFormulaActual.rootImageRadius_eq_rootNorm (T := T) (b := b)

/-- Re-export: `rootImageRadius_b = p_b ^ (-(c_norm_b)/(2l))`. -/
theorem rootImageRadius_eq_p_rpow_reexport :
    (rootImageRadius T b : Real) =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) :=
  S709RootImageRadiusFormulaActual.rootImageRadius_eq_p_rpow (T := T) (b := b)

/-- **Log form with the normalized coefficient**: `-(c_norm * log p)/(2l)`. -/
theorem log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL :
    Real.log (rootImageRadius T b : Real) =
      -(qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real)) /
        (2 * (l.value : Real)) := by
  rw [rootImageRadius_eq_p_rpow_reexport (T := T) (b := b)]
  have hp : (0 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  change Real.log ((qVFamTensorP T b : Real) ^
      (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)))) = _
  rw [Real.log_rpow hp]
  ring

/-- **Log form with the qVFamily order**, when the normalization correction is zero. -/
theorem log_rootImageRadius_eq_neg_order_mul_logp_div_twoL
    (hcorr : normalizedOrderCorrection T b = 0) :
    Real.log (rootImageRadius T b : Real) =
      -(((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)) /
        (2 * (l.value : Real)) := by
  rw [log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL]
  have hcoeff : qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) := by
    exact (sourceNormalization_correction_zero_iff (T := T) (b := b)).mp hcorr
  rw [hcoeff]

def radiusLogRows : List (String × String × String) :=
  [ ("radius = root norm", "rootImageRadius_b = rootNormedElementNorm_b", "S709 re-export"),
    ("p-rpow form", "rootImageRadius_b = p_b^(-(c_norm)/(2l))", "S709 re-export"),
    ("log coefficient form", "log rootImageRadius_b = -(c_norm*log p_b)/(2l)", "PROVED"),
    ("paper order form", "= -((qVFamily.order*log p_b)/(2l)) when correction = 0", "PROVED"),
    ("bridge remark", "radius coefficient -1/(2l); (sFactor(nC)-1)/(2l) arises from label/procession average", "STRUCTURAL") ]

theorem radiusLogRows_length : radiusLogRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual.log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual.log_rootImageRadius_eq_neg_order_mul_logp_div_twoL

end LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual

end