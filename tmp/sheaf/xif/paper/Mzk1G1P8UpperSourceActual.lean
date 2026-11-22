/- G1P8Upper source data: actual N5 condition and conditional packaging of the
remaining actual source facts into G1P8UpperSources / S2953 certificate. -/
import tmp.sheaf.xif.paper.Mzk1G1P8UpperActual
import tmp.sheaf.xif.paper.Mzk1G1P8CertificateActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8UpperSourceActual

open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8UpperActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8CertificateActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (label : Type) [Fintype label] [Nonempty label]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def g1p8QAbsLog {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) : Real :=
  abs (Real.log (Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T))))

/-- Actual N5 condition from the actual global q-pilot data. -/
theorem g1p8_actual_n5_condition :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  actual_n5_qSideSignedValueCondition T

/-- Package the actual source facts into G1P8UpperSources. -/
theorem g1p8UpperSources_nonempty
    (thetaLogVolume : Real)
    (hHull : arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T)
    (hM : 1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T)
    (htheta : (signedFloorCertificate (places := places) (tuple := tuple) label μ).thetaSigned =
      thetaLogVolume)
    (hC : CThetaPaper l (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0 =
      thetaLogVolume /
        g1p8QAbsLog T)
    (hupper : thetaLogVolume ≤
      CThetaPaper l (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0 *
        g1p8QAbsLog T) :
    Nonempty (G1P8UpperSources places tuple label μ T) :=
  ⟨{ hullLog_eq_neg_M := hHull
     M_ge_one := hM
     thetaLogVolume := thetaLogVolume
     htheta := htheta
     hCTheta := by simpa [g1p8QAbsLog] using hC
     hupper := by simpa [g1p8QAbsLog] using hupper }⟩

/-- Actual S2953 certificate from the source facts. -/
theorem g1p8_S2953Certificate_exists
    (thetaLogVolume : Real)
    (hHull : arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T)
    (hM : 1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T)
    (htheta : (signedFloorCertificate (places := places) (tuple := tuple) label μ).thetaSigned =
      thetaLogVolume)
    (hC : CThetaPaper l (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0 =
      thetaLogVolume /
        g1p8QAbsLog T)
    (hupper : thetaLogVolume ≤
      CThetaPaper l (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0 *
        g1p8QAbsLog T) :
    Nonempty (S2953CThetaUpperCertificate label l) :=
  ⟨g1p8_S2953Certificate places tuple label μ T
    (Classical.choose (g1p8UpperSources_nonempty places tuple label μ T thetaLogVolume
      hHull hM htheta (by simpa [g1p8QAbsLog] using hC)
      (by simpa [g1p8QAbsLog] using hupper)))⟩

#check g1p8_actual_n5_condition
#check g1p8UpperSources_nonempty
#check g1p8_S2953Certificate_exists

end LeanFormal.IUT.XiFPaper.Mzk1G1P8UpperSourceActual
end
