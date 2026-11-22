import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificate
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2716StageAQNormActual

universe u v w uL
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {W : iota -> Type w}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable (label : Type uL) [Fintype label] [Nonempty label]

/-- Stage A certificate package: an actual signed Step-XI certificate together
with an actual real qPilot whose signed value is the certificate's qSigned.
The qPilot here is the canonical real reconstructed from the actual hull log;
it is NOT asserted to be the paper source q-pilot (that remains a separate
source identification). -/
structure S2716QNormalizedSignedCertificate where
  cert : StepXIFiniteCertificateSigned label
  qPilot : Real
  qPilot_pos : 0 < qPilot
  qSide : cert.qSigned = -|Real.log qPilot|

/-- The actual canonical hull log of the arithmetic tuple. -/
abbrev S2716HullLog : Real :=
  arithmeticTupleCanonicalHullHaarLog places tuple mu

/-- Stage A actual bridge: the signed certificate from the actual hull, with
qPilot := exp (hullLog).  The equality `qSigned = -|log qPilot|` and
`qSigned <= hullVolume` are both proved, not assumed. -/
noncomputable def S2716QNormalizedCertificate
    (hneg : S2716HullLog places tuple mu < 0) :
    S2716QNormalizedSignedCertificate label :=
  { cert := arithmeticTupleSignedFiniteCertificate places tuple label mu hneg
    qPilot := Real.exp (S2716HullLog places tuple mu)
    qPilot_pos := Real.exp_pos _
    qSide := by
      change S2716HullLog places tuple mu =
        -|Real.log (Real.exp (S2716HullLog places tuple mu))|
      rw [Real.log_exp, abs_of_neg hneg, neg_neg] }

/-- The certificate qSigned is exactly `-|log qPilot|` for the reconstructed
actual qPilot. -/
theorem S2716_qSigned_eq_neg_abs_log
    (hneg : S2716HullLog places tuple mu < 0) :
    (S2716QNormalizedCertificate places tuple mu label hneg).cert.qSigned =
      -|Real.log (S2716QNormalizedCertificate places tuple mu label hneg).qPilot| :=
  (S2716QNormalizedCertificate places tuple mu label hneg).qSide

/-- The qSigned lower bound `qSigned <= hull.hullVolume` is the certificate's
actual `q_le_hull` field (not the vacuous `q = -1` endpoint). -/
theorem S2716_qSigned_le_hullVolume
    (hneg : S2716HullLog places tuple mu < 0) :
    (S2716QNormalizedCertificate places tuple mu label hneg).cert.qSigned <=
      (S2716QNormalizedCertificate places tuple mu label hneg).cert.hull.hullVolume :=
  (S2716QNormalizedCertificate places tuple mu label hneg).cert.q_le_hull

/-- qPilot lies in (0,1), since the actual hull log is negative. -/
theorem S2716_qPilot_mem_unit_interval
    (hneg : S2716HullLog places tuple mu < 0) :
    0 < (S2716QNormalizedCertificate places tuple mu label hneg).qPilot ∧
      (S2716QNormalizedCertificate places tuple mu label hneg).qPilot < 1 := by
  refine ⟨(S2716QNormalizedCertificate places tuple mu label hneg).qPilot_pos, ?_⟩
  change Real.exp (S2716HullLog places tuple mu) < 1
  exact Real.exp_lt_one_iff.mpr hneg


/-- The reconstructed qPilot satisfies the actual q-side signed-value condition
qSigned = -|log qPilot| (certificate-level; source q identification remains
separate). -/
theorem S2716_qSideSignedValueCondition
    (hneg : S2716HullLog places tuple mu < 0) :
    qSideSignedValueCondition
      (S2716QNormalizedCertificate places tuple mu label hneg).qPilot
      (S2716QNormalizedCertificate places tuple mu label hneg).cert.qSigned :=
  (S2716QNormalizedCertificate places tuple mu label hneg).qSide

/-- qSigned is strictly negative, since qPilot lies in (0,1). -/
theorem S2716_qSigned_neg
    (hneg : S2716HullLog places tuple mu < 0) :
    (S2716QNormalizedCertificate places tuple mu label hneg).cert.qSigned < 0 :=
  (S2716QNormalizedCertificate places tuple mu label hneg).cert.q_negative

/-- qSigned is bounded by the thetaSigned endpoint through the actual hull
inclusion. -/
theorem S2716_qSigned_le_thetaSigned
    (hneg : S2716HullLog places tuple mu < 0) :
    (S2716QNormalizedCertificate places tuple mu label hneg).cert.qSigned ≤
      (S2716QNormalizedCertificate places tuple mu label hneg).cert.thetaSigned :=
  le_trans (S2716_qSigned_le_hullVolume places tuple mu label hneg)
    (S2716QNormalizedCertificate places tuple mu label hneg).cert.hull_le_theta

/-- The normalized certificate forgotten to the existing Step-XI certificate
shape, with actual qSigned and qPilot. -/
noncomputable def S2716StepXICertificate
    (hneg : S2716HullLog places tuple mu < 0) :
    StepXIFiniteCertificate label :=
  (S2716QNormalizedCertificate places tuple mu label hneg).cert.toStepXIFiniteCertificate
#check S2716QNormalizedSignedCertificate
#check S2716QNormalizedCertificate
#check S2716_qSigned_eq_neg_abs_log
#check S2716_qSigned_le_hullVolume
#check S2716_qPilot_mem_unit_interval

end LeanFormal.IUT.XiFPaper.S2716StageAQNormActual
end