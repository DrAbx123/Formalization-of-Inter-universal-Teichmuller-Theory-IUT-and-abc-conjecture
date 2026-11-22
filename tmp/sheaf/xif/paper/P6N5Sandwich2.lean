/- P6 N5 sandwich 2: fully qualified P5 objects. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110N5Final
import tmp.sheaf.xif.paper.Node09P5HullInequalityFinalActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P6N5Sandwich2
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Final
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorBlock T b)]
variable [BorelSpace (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorBlock T b)]
noncomputable def paperSandwichM2 (Q : Real) : Real := Q / (2 * (l.value : Real))
theorem p6N5Sandwich2_le_theta {Q : Real}
    (hM : LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual.qVFamNormalizedQPilotVolume T b =
      paperSandwichM2 (l := l) Q) :
    paperSandwichM2 (l := l) Q ≤
      LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume
        (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorPlaces T b)
        (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorTuple T b)
        MeasureTheory.Measure.addHaar
        (LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual.qVFamLocalThetaHull T b) := by
  rw [← hM]
  exact LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual.qVFamNormalizedQPilotVolume_le_thetaHullVolume T b
theorem n5_and_sandwich2 {Q : Real}
    (hM : LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual.qVFamNormalizedQPilotVolume T b =
      paperSandwichM2 (l := l) Q) :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) ∧
      paperSandwichM2 (l := l) Q ≤
        LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume
          (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorPlaces T b)
          (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorTuple T b)
          MeasureTheory.Measure.addHaar
          (LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual.qVFamLocalThetaHull T b) :=
  ⟨n5_final T, p6N5Sandwich2_le_theta T b hM⟩
#check paperSandwichM2
#check p6N5Sandwich2_le_theta
#check n5_and_sandwich2
end LeanFormal.IUT.XiFPaper.P6N5Sandwich2
end
