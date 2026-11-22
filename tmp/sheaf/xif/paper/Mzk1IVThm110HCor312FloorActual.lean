import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificateNonvacuous
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVLambda
import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import Mathlib.Tactic
/-! hCor312 from the actual arithmetic-tuple signed floor certificate.

The StepXI certificate is the actual
`arithmeticTupleSignedFloorCertificate` (FinitePlaceIQHullSignedCertificateNonvacuous).
The two remaining source objects are explicit:
* N5: `qSideSignedValueCondition qPilot certificate.qSigned`;
* CThetaPaper normalization `CThetaPaper ... = thetaLogVolume / |log qPilot|`.
No fake/sorry/extra axiom. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
open LeanFormal.IUT
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
universe u v w uL
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- The actual StepXI signed floor certificate at the arithmetic-tuple layer. -/
abbrev signedFloorCertificate (label : Type) [Fintype label] [Nonempty label]
    (μ : MeasureTheory.Measure (ArithmeticTensorTupleBlock places tuple))
    [MeasureTheory.Measure.IsAddHaarMeasure μ] : StepXIFiniteCertificateSigned label :=
  arithmeticTupleSignedFloorCertificate places tuple label μ
/-- Build the S2953 upper certificate from the actual floor certificate, the N5 source
q-pilot condition, and the CThetaPaper source normalization. -/
def certificateOfFloorData
    (label : Type) [Fintype label] [Nonempty label]
    (l : PrimeGeFive) (μ : MeasureTheory.Measure (ArithmeticTensorTupleBlock places tuple))
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (qPilot logQ dmod dFpd fFpd eStar etaPrm thetaLogVolume : Real)
    (hqne : Real.log qPilot ≠ 0)
    (hN5 : qSideSignedValueCondition qPilot
      (signedFloorCertificate places tuple label μ).qSigned)
    (htheta : (signedFloorCertificate places tuple label μ).thetaSigned = thetaLogVolume)
    (hCTheta : CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm =
      thetaLogVolume / |Real.log qPilot|) :
    S2953CThetaUpperCertificate label l where
  certificate := (signedFloorCertificate places tuple label μ).toStepXIFiniteCertificate
  q := qPilot
  logQ := logQ
  dmod := dmod
  dFpd := dFpd
  fFpd := fFpd
  eStar := eStar
  etaPrm := etaPrm
  thetaLogVolume := thetaLogVolume
  htheta := htheta
  hqAbs := by
    exact (neg_qSideSignedValueCondition_eq_abs hN5).symm
  hCTheta := hCTheta
  hupper := by
    rw [hCTheta]
    have hqpos : 0 < |Real.log qPilot| := abs_pos.mpr hqne
    field_simp [hqpos.ne']
    rfl
/-- hCor312 from the actual floor certificate + N5 + CThetaPaper normalization. -/
theorem hCor312_of_floor_data
    (label : Type) [Fintype label] [Nonempty label]
    (T : Thm110DisplayTerms) (l : PrimeGeFive) (dFpd fFpd : Real)
    (μ : MeasureTheory.Measure (ArithmeticTensorTupleBlock places tuple))
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (qPilot logQ dmod dFpd' fFpd' eStar etaPrm thetaLogVolume : Real)
    (hqne : Real.log qPilot ≠ 0)
    (hN5 : qSideSignedValueCondition qPilot
      (signedFloorCertificate places tuple label μ).qSigned)
    (htheta : (signedFloorCertificate places tuple label μ).thetaSigned = thetaLogVolume)
    (hCTheta : CThetaPaper l logQ dmod dFpd' fFpd' eStar etaPrm =
      thetaLogVolume / |Real.log qPilot|)
    (hlogQpos : 0 < logQ) (hlogQposT : 0 < T.logQ)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : T.logQ = logQ) (hdmod : T.dmod = dmod)
    (hdFpd : dFpd = dFpd') (hfFpd : fFpd = fFpd')
    (heStar : T.eStar = eStar) (hetaPrm : T.etaPrm = etaPrm) :
    thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T :=
  hCor312_of_actual_certificate T l dFpd fFpd
    (certificateOfFloorData places tuple label l μ qPilot logQ dmod dFpd' fFpd'
      eStar etaPrm thetaLogVolume hqne hN5 htheta hCTheta)
    hqne hlogQpos hL hD hF hlogQ hdmod hdFpd hfFpd heStar hetaPrm hlogQposT
/-- Exact first missing source objects. -/
def exactMissingSourceObjects : List String :=
  [ "N5: actual source q-pilot and qSideSignedValueCondition qPilot certificate.qSigned",
    "CThetaPaper source normalization: CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm = thetaLogVolume / |log qPilot|",
    "source identification of logQ,dmod,dFpd,fFpd,eStar,etaPrm with actual local/global data" ]
theorem exactMissingSourceObjects_length : exactMissingSourceObjects.length = 3 := rfl
#check certificateOfFloorData
#check hCor312_of_floor_data
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
end
