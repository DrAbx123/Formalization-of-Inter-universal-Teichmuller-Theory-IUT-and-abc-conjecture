import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamRootCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

-- Paper-level xi-f target: separated q and Theta normalizations
--
-- Both sides use the normalized spectral coefficient c_norm:
-- q side: sum_b nativeBadLocalWeight b * c_norm_b * log p_b, where
--   c_norm_b = QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b and p_b = qVFamTensorP T b.
-- Theta side: root coefficient c_norm_b/(2l) = qVFamPaperRootCoefficient T b,
-- used in the actual root theta closure hull and its normalized log.
-- No default/Completion norm is used.
-- WRITE-ONLY; local compile after write.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamRootCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

-- Weighted normalized q-pilot magnitude:
-- sum_b weight_b * c_norm_b * log p_b.
noncomputable def actualQPilotMagnitudeClassical : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real))

noncomputable def actualQPilotSignedLogClassical : Real :=
  -actualQPilotMagnitudeClassical (l := l) T

-- Actual root coefficient at b: c_norm/(2l).
noncomputable def actualRootCoeff
    (b : Bad (nativePlaceSelection T)) : qVFamTensorV → Real :=
  fun _ => QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
    (2 * l.value : Real)

theorem actualRootCoeff_eq_normalized_div
    (b : Bad (nativePlaceSelection T)) :
    actualRootCoeff (l := l) T b =
      fun _ => QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
        (2 * l.value : Real) := by
  funext i
  unfold actualRootCoeff
  rfl

-- Actual root theta scaled region at label j.
noncomputable def actualRootThetaRegion
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (fun _ : qVFamTensorV =>
      ((gaussExponent j.1).toNat : Real) * actualRootCoeff T b ())

noncomputable def actualRootThetaImageSet
    (b : Bad (nativePlaceSelection T)) : Set (qVFamTensorBlock T b) :=
  ⋃ j : SignedLabel l.value, actualRootThetaRegion (l := l) T b j

noncomputable def actualRootThetaHull
    (b : Bad (nativePlaceSelection T)) : Set (qVFamTensorBlock T b) :=
  closure (actualRootThetaImageSet (l := l) T b)

-- Actual local hull region: the actual root theta closure hull.
noncomputable abbrev actualLocalHullRegion
    (b : Bad (nativePlaceSelection T)) : Set (qVFamTensorBlock T b) :=
  actualRootThetaHull (l := l) T b

theorem actualLocalHullRegion_eq_root_closure
    (b : Bad (nativePlaceSelection T)) :
    actualLocalHullRegion (l := l) T b =
      closure (actualRootThetaImageSet (l := l) T b) := rfl

-- Actual local normalized hull log on the root closure hull.
noncomputable def actualLocalHullLog
    (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple
    Measure.addHaar
    (actualLocalHullRegion (l := l) T b)

noncomputable def actualThetaHullLogRoot : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * actualLocalHullLog (l := l) T b

noncomputable def actualThetaHullMagnitudeRoot : Real :=
  -actualThetaHullLogRoot (l := l) T

def ActualPaperXiFTarget : Prop :=
  actualQPilotSignedLogClassical (l := l) T ≤
    actualThetaHullLogRoot (l := l) T

def ActualPaperXiFTargetMagnitude : Prop :=
  actualThetaHullMagnitudeRoot (l := l) T ≤
    actualQPilotMagnitudeClassical (l := l) T

theorem actualPaperXiFTarget_iff_magnitude :
    ActualPaperXiFTarget (l := l) T ↔
      ActualPaperXiFTargetMagnitude (l := l) T := by
  unfold ActualPaperXiFTarget ActualPaperXiFTargetMagnitude
  unfold actualQPilotSignedLogClassical actualThetaHullMagnitudeRoot
  constructor <;> intro h <;> linarith

-- Weight normalization.
theorem actualTargetWeight_eq_inv
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv T b

theorem actualTargetWeight_nonneg
    (b : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b := by
  rw [actualTargetWeight_eq_inv]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem actualTargetWeightedSum_weights_recorded :
    (∀ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b =
        ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹)
      ∧ (∀ b : Bad (nativePlaceSelection T), 0 ≤ nativeBadLocalWeight T b) :=
  ⟨actualTargetWeight_eq_inv (l := l) T, actualTargetWeight_nonneg (l := l) T⟩

#print QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient
#print actualQPilotMagnitudeClassical
#print actualRootCoeff
#check actualQPilotMagnitudeClassical
#check actualQPilotSignedLogClassical
#check actualRootCoeff
#check actualRootThetaRegion
#check actualRootThetaHull
#check actualLocalHullRegion_eq_root_closure
#check actualLocalHullLog
#check actualThetaHullLogRoot
#check ActualPaperXiFTarget
#check actualPaperXiFTarget_iff_magnitude

end LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual

end