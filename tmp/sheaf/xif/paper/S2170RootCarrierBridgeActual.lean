import tmp.sheaf.xif.paper.S2157RootCoefficientActual
import tmp.sheaf.xif.paper.S826CNormOrderRamificationActual
import tmp.sheaf.xif.paper.S2154NormalizedSupplyActual
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S2170RootCarrierBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2157RootCoefficientActual
open LeanFormal.IUT.XiFPaper.S2154NormalizedSupplyActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The e=1 normalization is exactly the scalar condition needed by S2157. -/
theorem s2170_hcNorm_iff_e_eq_one (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) :
    (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
        ((qVFamily T b).order : Real)) ↔ e = 1 :=
  qVFamNormalizedCoefficient_eq_order_iff_e_eq_one (l := l) T b e hepos hcomp
/-- Under e=1 and the normalized norm compatibility, the actual root generator
has the paper root coefficient norm p^(-(order/(2l))). -/
theorem s2170_rootGenerator_norm_of_e_eq_one (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) (he : e = 1) :
    ‖s2157RootCoefficientGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamPaperRootCoefficient T b)) :=
  s2157RootCoefficientGenerator_norm (l := l) T b
    ((s2170_hcNorm_iff_e_eq_one (l := l) T b e hepos hcomp).mpr he)
/-- Exact target-level missing piece: a CommonPrimeCompletion generator with
the paper root coefficient norm.  The S2157 generator lives in
rootNormedAmbient, not in the completion. -/
def s2170CompletionRootGeneratorMissing : Prop :=
  Nonempty (s2154GeneratorAt T b (qVFamPaperRootCoefficient T b))
/-- The completion generator is not supplied by the root-ambient generator;
this is the exact carrier bridge gap. -/
def s2170RootAmbientToCompletionBridgeMissing : Prop :=
  Nonempty (s2157RootCarrier T b → CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))
#print axioms s2170_hcNorm_iff_e_eq_one
#print axioms s2170_rootGenerator_norm_of_e_eq_one
end LeanFormal.IUT.XiFPaper.S2170RootCarrierBridgeActual
end
