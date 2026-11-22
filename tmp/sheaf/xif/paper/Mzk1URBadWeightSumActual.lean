/- U-C Step (viii) (beta): the actual bad-place weight total (kurt, Lead item 4).

From the actual definitions in VbadPlaceIndexingActual:

  nativeBadLocalWeight T b = localNormalizedWeight T.arithmetic (nativeBadToKPlace T b)
                            = (localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Real)^{-1}

(proved there by rfl).  Hence the total bad weight is the sum of the inverse
actual completion degrees; no closed form (in particular no equality with the
paper modified degree d_mod and no equality with 1) follows from the
definitional data - the tree has d_mod only as a paper parameter
(ExplicitConstantObject.dmod : Real, and a numeric placeholder
Mzk1Stage4HeightRegionNumericsActual.dMod : Nat := 1), so the paper
identification is a retained condition with explicit provenance.

This file records the actual expression, its nonnegativity, and the two named
retained conditions consumed by hstepVIII / htheta (no sorry, no axiom). -/
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URBadWeightSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual total bad-place weight: sum of inverse actual completion degrees
(directly from the definition of nativeBadLocalWeight). -/
theorem urBadWeightSum_eq_invDegree :
    (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b) =
      ∑ b : Bad (nativePlaceSelection T),
        ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : ℕ) : ℝ)⁻¹ := by
  exact Finset.sum_congr rfl (fun b _ => nativeBadLocalWeight_eq_inv (T := T) b)

/-- The actual total bad-place weight is nonnegative. -/
theorem urBadWeightSum_nonneg :
    0 ≤ ∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b :=
  Finset.sum_nonneg (fun b _ => by
    rw [nativeBadLocalWeight_eq_inv (T := T)]
    exact inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Retained condition (paper IUT IV Step (iii)/(v)-(vi)): the actual total bad
weight equals the paper modified degree d_mod.  Not derivable from the
definitional data (d_mod is only a paper parameter in the tree). -/
def BadWeightTotalEqDmod (dmod : ℝ) : Prop :=
  (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b) = dmod

/-- Retained bridge shape for hstepVIII with aggregate letters (no normalization
assumption): the actual bad-weighted sum of log p_b is at most log s^Q (paper
Step (iii) d_mod normalization; provenance = IUT IV). -/
def BadWeightedLogPBridge (logSQ : ℝ) : Prop :=
  (∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * Real.log (qVFamTensorP T b : ℝ)) ≤ logSQ

#print axioms urBadWeightSum_eq_invDegree
#print axioms urBadWeightSum_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1URBadWeightSumActual
end