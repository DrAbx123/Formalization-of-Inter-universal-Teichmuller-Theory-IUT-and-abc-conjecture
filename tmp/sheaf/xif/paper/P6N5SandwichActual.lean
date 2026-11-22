/- P6 N5 sandwich: qVFam volume = Q/(2l) gives Q/(2l) <= theta hull. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110N5Final
import tmp.sheaf.xif.paper.Node09P5HullInequalityFinalActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P6N5SandwichActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Final
open MeasureTheory
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
/-- Paper sandwich value M = Q/(2l). -/
noncomputable def paperSandwichM (Q : Real) : Real := Q / (2 * (l.value : Real))
/-- If the actual qVFam volume is M=Q/(2l), the P5 inequality gives
M <= theta hull volume. -/
theorem p6N5Sandwich_le_theta {Q : Real}
    (hM : qVFamNormalizedQPilotVolume T b = paperSandwichM (l := l) Q) :
    paperSandwichM (l := l) Q ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (qVFamLocalThetaHull T b) := by
  rw [← hM]
  exact qVFamNormalizedQPilotVolume_le_thetaHullVolume T b
/-- N5 condition together with the sandwich-to-theta inequality. -/
theorem n5_and_sandwich {Q : Real}
    (hM : qVFamNormalizedQPilotVolume T b = paperSandwichM (l := l) Q) :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) ∧
      paperSandwichM (l := l) Q ≤
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
          Measure.addHaar (qVFamLocalThetaHull T b) :=
  ⟨n5_final T, p6N5Sandwich_le_theta T b hM⟩
#check paperSandwichM
#check p6N5Sandwich_le_theta
#check n5_and_sandwich
end LeanFormal.IUT.XiFPaper.P6N5SandwichActual
end
