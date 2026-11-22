/- U-R C2 q-side normalisation (route §5.4: `M = Q/(2l)`).

The accepted `actualQPilotMagnitudeClassical` is the *unrooted* q magnitude
`Q = sum_b w_b c_norm_b log p`; the paper's `M` is `Q/(2l)`.  This file
proves the actual normalisation identity

  `(1/(2l)) Q = - sum_b w_b (1/(2l)) log ‖q_b‖`

through the actual identifiers: `c_norm_b` is the actual `localNormOrder` of the
actual qVFamily q (spectral norm), and the actual q log-norm is related to the
actual `localNormOrder` by `urRootQ_log_norm_order` of
`Mzk1URRootExtInstancesActual` (proved from the same root extension used for the
mass identity).  No `rfl`-tautology, no surrogate, no axiom/sorry. -/
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1URQNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual normalized q coefficient `c_norm` is the actual `localNormOrder`
of the actual qVFamily q (spectral-norm normalisation). -/
theorem ur_cNorm_eq_localNormOrder :
    qVFamNormalizedCoefficient T b =
      localNormOrder (qVFamTensorP T b) (qVFamNormalizedGenerator T b) := by
  unfold qVFamNormalizedCoefficient localNormOrder
  simp only [Real.logb]
  rw [neg_div]

/-- The actual qVFamily q of the normalized coefficient is the same actual element as
`sourceRootQUnit` on the actual root base field (both are the qVFamily q; only the
definitional unfolding of `qVFamTensorPlaces`/`sourceRootField` is required). -/
theorem ur_gen_eq_sourceRootQUnit :
    (qVFamNormalizedGenerator T b : rootBase T b) =
      (sourceRootQUnit T b : rootBase T b) := by
  unfold qVFamNormalizedGenerator sourceRootQUnit
  rfl

/-- **C2 q-side normalisation** (route §5.4 `M = Q/(2l)`): the half q-pilot
magnitude is the actual weighted sum of the per-b actual q log-masses
`(1/(2l)) log ‖q_b‖`, with the actual bad-place weights. -/
theorem urM_eq_half_qMagnitude :
    (1 / (2 * (l.value : ℝ))) * actualQPilotMagnitudeClassical (l := l) T =
      -∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((1 / (2 * (l.value : ℝ))) *
            Real.log ‖((sourceRootQUnit T b : rootBase T b))‖) := by
  unfold actualQPilotMagnitudeClassical
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hc := ur_cNorm_eq_localNormOrder (T := T) (b := b)
  have hg := ur_gen_eq_sourceRootQUnit (T := T) (b := b)
  have hlog := urRootQ_log_norm_order (T := T) (b := b)
  rw [hc, hg, hlog]
  rw [neg_mul, mul_neg, mul_neg, neg_neg]
  ac_rfl

#print axioms ur_cNorm_eq_localNormOrder
#print axioms ur_gen_eq_sourceRootQUnit
#print axioms urM_eq_half_qMagnitude

end LeanFormal.IUT.XiFPaper.Mzk1URQNormalizationActual
end