import tmp.sheaf.xif.paper.S2170RootCarrierBridgeActual
import tmp.sheaf.xif.paper.S2040QVPlaceSplitActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalStructureInstances
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalStructureInstances
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S2176RamificationE1Actual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2170RootCarrierBridgeActual
open LeanFormal.IUT.XiFPaper.S2157RootCoefficientActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The actual qVFamily place is unramified over its rational prime. -/
def s2176QVFamUnramified : Prop :=
  localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1
/-- The e=1 normalization hcNorm is exactly the unramified condition of the
qVFamily place, under the actual normalized norm compatibility. -/
theorem s2176_hcNorm_iff_unramified
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b
      (localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) : Real)) :
    (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
        ((qVFamily T b).order : Real)) ↔ s2176QVFamUnramified T b := by
  unfold s2176QVFamUnramified
  have hepos : (0 : Real) < (localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) : Real) := by
    have hfin := instModuleFiniteAdicCompletionIntegers (k := ℚ) (K := T.arithmetic.F) (qVFamTensorPlace T b)
    exact_mod_cast (one_le_localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) hfin)
  constructor
  · intro h
    exact_mod_cast (s2170_hcNorm_iff_e_eq_one (l := l) T b
      (localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) : Real) hepos hcomp).mp h
  · intro h
    exact (s2170_hcNorm_iff_e_eq_one (l := l) T b
      (localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) : Real) hepos hcomp).mpr
      (by exact_mod_cast h)
/-- Under the unramified condition and norm compatibility, the actual root
generator has the paper root coefficient norm. -/
theorem s2176_rootGenerator_norm_of_unramified
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b
      (localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) : Real))
    (hunr : s2176QVFamUnramified T b) :
    ‖s2157RootCoefficientGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamPaperRootCoefficient T b)) :=
  s2170_rootGenerator_norm_of_e_eq_one (l := l) T b
    (localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) : Real)
    (by
    have hfin := instModuleFiniteAdicCompletionIntegers (k := ℚ) (K := T.arithmetic.F) (qVFamTensorPlace T b)
    exact_mod_cast (one_le_localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) hfin))
    hcomp (by exact_mod_cast hunr)
/-- Exact missing: the unramified condition for the actual qVFamily place. -/
abbrev s2176QVFamUnramifiedRequired : Prop :=
  S2040QVPlaceUnramifiedRequired T b
/-- Exact missing target-level carrier bridge: the root ambient generator is
not identified with a CommonPrimeCompletion generator. -/
def s2176CompletionCarrierBridgeMissing : Prop :=
  Nonempty (s2157RootCarrier T b → CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))
#print axioms s2176_hcNorm_iff_unramified
#print axioms s2176_rootGenerator_norm_of_unramified
end LeanFormal.IUT.XiFPaper.S2176RamificationE1Actual
end
