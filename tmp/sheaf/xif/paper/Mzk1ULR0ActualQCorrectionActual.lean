/- R0.1 legacy-normalization correction (route 2.1 flag):
   legacy actualQPilotMagnitudeClassical uses cSpectral = GeneratorSupply.qVFamNormalizedCoefficient;
   donor BadPlacePaperNormalizedComparisonActual.c_norm_eq_paperCoefficient_sub_normRatio:
     cSpectral = paperNormalizedCoefficient - log(qVFamNormRatio)/log p;
   paper q-coefficient (order-based) = paperNormalizedCoefficient = order * rationalDegreeFactor * (log baseNorm/log p).
   So legacy actualQ = paper-coefficient version - per-b normRatio correction; equal termwise iff qVFamNormRatio = 1
   (and further order-form iff rationalDegreeFactor*log baseNorm/logp = 1).
   Document: legacy spectral object is NOT paper c_P; correction is explicit, no invented equality. -/
import tmp.sheaf.xif.paper.Mzk1ULR0RealDictionaryActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeFactorActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0ActualQCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- legacy actualQ 的逐 b 项（spectral coefficient）。 -/
noncomputable def actualQTermSpectral (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b *
    (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
      Real.log (qVFamTensorP T b : Real))

/-- paper-coefficient 版（order-based paperNormalizedCoefficient）的逐 b 项。 -/
noncomputable def actualQTermPaper (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b *
    (paperNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real))

/-- 逐 b 精确修正: spectral = paper - log(qVFamNormRatio)/log p。 -/
theorem actualQTerm_eq_paper_sub_normRatio (b : Bad (nativePlaceSelection T)) :
    actualQTermSpectral (l := l) T b =
      actualQTermPaper (l := l) T b -
        nativeBadLocalWeight T b *
          (Real.log (qVFamNormRatio T b) / Real.log (qVFamTensorP T b : Real)) *
            Real.log (qVFamTensorP T b : Real) := by
  unfold actualQTermSpectral actualQTermPaper
  rw [c_norm_eq_paperCoefficient_sub_normRatio]
  ring

/-- qVFamNormRatio = 1 ⇒ 逐 b spectral 项 = paper 项。 -/
theorem actualQTerm_eq_paper_of_normRatio_one (b : Bad (nativePlaceSelection T))
    (h : qVFamNormRatio T b = 1) :
    actualQTermSpectral (l := l) T b = actualQTermPaper (l := l) T b := by
  have h' := actualQTerm_eq_paper_sub_normRatio (l := l) T b
  rw [h, Real.log_one, zero_div] at h'
  simp only [zero_mul, mul_zero, sub_zero] at h'
  exact h'

#print axioms actualQTerm_eq_paper_sub_normRatio
#print axioms actualQTerm_eq_paper_of_normRatio_one

end LeanFormal.IUT.XiFPaper.Mzk1ULR0ActualQCorrectionActual