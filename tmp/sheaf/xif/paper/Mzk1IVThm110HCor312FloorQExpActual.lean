/- Floor qSigned via exp: actual N5 condition and hCor312 floor wrapper. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312FloorActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual
import tmp.sheaf.xif.paper.Mzk1IVThm110N5FloorBridgeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorQExpActual

open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5FloorBridgeActual
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

/-- Actual N5 condition for qPilot = exp(qSigned): qSigned = -|log (exp qSigned)|. -/
theorem floorQExp_qSideSignedValueCondition :
    qSideSignedValueCondition
      (Real.exp ((signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned))
      (signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned := by
  unfold qSideSignedValueCondition
  rw [Real.log_exp]
  rw [abs_of_neg ((signedFloorCertificate (places := places) (tuple := tuple) label μ).q_negative)]
  ring

/-- exp of the floor qSigned has nonzero log. -/
theorem floorQExp_log_ne_zero :
    Real.log (Real.exp
      ((signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned)) ≠ 0 := by
  rw [Real.log_exp]
  exact ne_of_lt ((signedFloorCertificate (places := places) (tuple := tuple) label μ).q_negative)

/-- S2953 certificate from the floor certificate with qPilot = exp(floor qSigned),
given the actual thetaLogVolume and CThetaPaper normalization. -/
noncomputable def floorQExpCertificate
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm thetaLogVolume : Real)
    (htheta : (signedFloorCertificate (places := places) (tuple := tuple) label μ).thetaSigned =
      thetaLogVolume)
    (hCTheta : CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm =
      thetaLogVolume / |Real.log
        (Real.exp ((signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned))|) :
    S2953CThetaUpperCertificate label l :=
  certificateOfFloorData places tuple label l μ
    (Real.exp ((signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned))
    logQ dmod dFpd fFpd eStar etaPrm thetaLogVolume
    (floorQExp_log_ne_zero places tuple label μ)
    (floorQExp_qSideSignedValueCondition places tuple label μ)
    htheta hCTheta

#check floorQExp_qSideSignedValueCondition
#check floorQExp_log_ne_zero
#check floorQExpCertificate

end LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorQExpActual
end
