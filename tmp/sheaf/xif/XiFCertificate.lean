import tmp.sheaf.xif.SourceXiFConstruction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringSigned
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume

/-!
# Value-layer xi-f certificate

This file consumes the value-layer xi-f inclusion of
tmp/sheaf/xif/SourceXiFConstruction.lean into the finite signed
certificate interface `StepXIFiniteCertificateSigned`.

SCOPE: value-layer/surrogate only. This is NOT paper-level xi-f and does
not claim `target_accepted`. Exact object/statement mismatches (see
tmp/sheaf/xif/XiF-AUDIT.md, task-491):

* sourceQPilotPoint is the Theta-pilot point at signed label 1, not the
  q-pilot object at (1,0).
* sourceQPilotLogVolume is card(SourceVolumeIndex l) * log(thetaPacket.q)
  (861*log q at l=41), not the paper value -|log q|.
* sourceThetaHullLogVolume is the supremum of pointwise source log-degrees
  over the value-monoid hull, not the procession-normalized log-volume of
  the paper 1,circ U holomorphic hull.
* sourceXiFInclusion is a pointwise hull-sup inequality, not membership
  -|log q| in R_{<= -|log Theta|}; it depends on hq<1 and hScaling.

The certificate below is therefore a value-layer consumer of the surrogate
inclusion, recorded so downstream work can separate it from the paper
object layer. No sorry, axiom, or toy carrier is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.OriginalInput

open LeanFormal.IUT

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Value-layer finite hull for the surrogate certificate: the certificate's
hull volume and per-label volume are both the surrogate Theta-hull scalar.
This is a finite-certificate abstraction, not the paper 1,circ U hull. -/
def valueLayerFiniteHull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hqlt : (I.theaterAt 0 0).thetaPacket.q < 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    FiniteHull (SourceVolumeIndex l) where
  volume _ := I.sourceThetaHullLogVolume v R n
  hullVolume := I.sourceThetaHullLogVolume v R n
  contains _ := le_rfl

/-- Uniform finite weights over the actual source volume index. -/
def valueLayerWeightedValues (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : WeightedValues (SourceVolumeIndex l) where
  value _ := I.sourceThetaHullLogVolume v R n
  weight _ := 1
  weightTotal := (Fintype.card (SourceVolumeIndex l) : ℝ)
  weightTotal_pos := by
    exact_mod_cast (sourceVolumeIndex_card_pos l)
  weightTotal_eq_sum := by
    simp

/-- The value-layer signed certificate: the surrogate q-pilot log-volume is
the raw source q-point log-degree; the surrogate hull/theta value is the
value-layer hull supremum; `q_le_hull` is exactly the source surrogate xi-f
inclusion. -/
def valueLayerCertificate (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hqlt : (I.theaterAt 0 0).thetaPacket.q < 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    StepXIFiniteCertificateSigned (SourceVolumeIndex l) where
  hull := valueLayerFiniteHull (I := I) v R n hqlt hScaling
  weighted := valueLayerWeightedValues (I := I) v R n
  weighted_matches_hull := by
    intro i
    rfl
  weights_nonnegative := by
    intro i
    show (0 : ℝ) ≤ (1 : ℝ)
    norm_num
  qSigned := I.sourceQPilotLogVolume v R n
  thetaSigned := I.sourceThetaHullLogVolume v R n
  q_le_hull := I.sourceXiFInclusion v R n hqlt.le hScaling
  hull_le_theta := le_rfl
  q_negative := by
    have hqpos : 0 < (I.theaterAt 0 0).thetaPacket.q := (I.theaterAt 0 0).thetaPacket.q_pos
    have hlog : Real.log ((I.theaterAt 0 0).thetaPacket.q) < 0 :=
      Real.log_neg hqpos hqlt
    rw [I.sourceQPilotLogVolume_eq_gauss v R n]
    exact mul_neg_of_pos_of_neg
      (by exact_mod_cast (sourceVolumeIndex_card_pos l)) hlog

/-- The signed certificate's q_le_hull slot is exactly the source value-layer
xi-f inclusion; no extra inequality input is hidden here. -/
theorem valueLayerCertificate_q_le_hull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hqlt : (I.theaterAt 0 0).thetaPacket.q < 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    (valueLayerCertificate (I := I) v R n hqlt hScaling).qSigned ≤
      (valueLayerCertificate (I := I) v R n hqlt hScaling).hull.hullVolume :=
  I.sourceXiFInclusion v R n hqlt.le hScaling

/-- The value-layer signed q <= theta conclusion (the certificate's
qSigned <= thetaSigned), explicitly not the paper xi-f membership. -/
theorem valueLayerCertificate_q_le_theta (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hqlt : (I.theaterAt 0 0).thetaPacket.q < 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    (valueLayerCertificate (I := I) v R n hqlt hScaling).qSigned ≤
      (valueLayerCertificate (I := I) v R n hqlt hScaling).thetaSigned :=
  le_trans
    (valueLayerCertificate (I := I) v R n hqlt hScaling).q_le_hull
    (valueLayerCertificate (I := I) v R n hqlt hScaling).hull_le_theta

end LeanFormal.IUT.Theorem311Source.OriginalInput

end
