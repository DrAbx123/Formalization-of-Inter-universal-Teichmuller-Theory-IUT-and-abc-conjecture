/- G1/P8 upper source: floor qSigned bridge reduction and construction of the
S2953 CTheta upper certificate from explicit actual source objects
(hullLog = -M, M>=1, thetaLogVolume, CTheta normalization, CTheta upper). -/
import tmp.sheaf.xif.paper.Mzk1G1P8CertificateActual
import tmp.sheaf.xif.paper.Mzk1IVThm110FloorNativeHullActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312FloorActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8UpperActual

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
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5FloorBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeHullActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

universe u v w uL

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

/-- Floor qSigned equals native qSigned once hullLog = -M and 1 <= M are supplied. -/
theorem g1p8_floor_native_qSigned
    (hM : arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T)
    (hMone : 1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T) :
    (signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned =
      S3013QSigned T :=
  floorQSigned_eq_native_of_hull places tuple label μ hM hMone

/-- Source objects needed for the unconditional S2953 CTheta upper certificate. -/
structure G1P8UpperSources where
  hullLog_eq_neg_M : arithmeticTupleCanonicalHullHaarLog places tuple μ =
    -nativeGlobalQPilotNormalizedLogMagnitude T
  M_ge_one : 1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T
  thetaLogVolume : Real
  htheta : (signedFloorCertificate (places := places) (tuple := tuple) label μ).thetaSigned =
    thetaLogVolume
  hCTheta : CThetaPaper l (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0 =
    thetaLogVolume / |Real.log (Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T)))| 
  hupper : thetaLogVolume ≤
    CThetaPaper l (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0 *
      |Real.log (Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T)))|

/-- The S2953 CTheta upper certificate from explicit actual source objects. -/
noncomputable def g1p8_S2953Certificate (S : G1P8UpperSources places tuple label μ T) :
    S2953CThetaUpperCertificate label l :=
  certificateOfFloorData places tuple label l μ
    (Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T)))
    (nativeGlobalQPilotNormalizedLogMagnitude T) 1 1 1 0 0
    S.thetaLogVolume
    (by
      rw [Real.log_exp]
      have := S.M_ge_one
      linarith)
    (by
      have hq := floorQSigned_eq_native_of_hull places tuple label μ
        S.hullLog_eq_neg_M S.M_ge_one
      have hcond : qSideSignedValueCondition
          (Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T)))
          (signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned := by
        rw [hq]
        unfold qSideSignedValueCondition S3013QSigned nativeGlobalQPilotNormalizedSignedLogVolume
        rw [Real.log_exp]
        rw [abs_neg, abs_of_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one S.M_ge_one))]
      exact hcond)
    S.htheta S.hCTheta

#check g1p8_floor_native_qSigned
#check G1P8UpperSources
#check g1p8_S2953Certificate

end LeanFormal.IUT.XiFPaper.Mzk1G1P8UpperActual
end
