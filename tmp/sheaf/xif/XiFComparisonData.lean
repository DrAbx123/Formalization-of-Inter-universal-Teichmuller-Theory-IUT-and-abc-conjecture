import tmp.sheaf.xif.XiFQPilot
import tmp.sheaf.xif.XiFHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # XIF-3 value-layer comparison data (explicit surrogate, not paper xi-f)

STATUS: value-layer/surrogate only. This file does NOT prove paper-level xi-f
and does NOT claim target_accepted.

Reconciled with the final XIF-1/XIF-2 value-layer declarations:
* XiFQPilot.sourceNormalizedQPilotLogVolume = raw card*log q divided by
  card(SourceVolumeIndex l), equal to Real.log thetaPacket.q;
* XiFHullVolume supplies sourceThetaHullLogVolume nonpositivity/finiteness under
  the same contracted-generator hypotheses and explicitly labels itself a
  value-layer surrogate.

Paper-level targets (not constructed here):
* the (1,0) q-pilot object, not the theta label 1 point;
* the signed procession-normalized -|log q|;
* the compact 1,circ U_{j,vQ}/IQ-carrier holomorphic hull volume -|log Theta|;
* paper xi-f inclusion in the paper's R_{<= -|log Theta|}.

Exact mismatches recorded:
1. q-pilot object: theta label 1, not the actual (1,0) q-pilot object.
2. q volume: normalized log q; equals -|log q| only under q <= 1 and q != 1.
3. Theta hull: sSup of pointwise log-degrees / card, not the paper compact
   1,circ U / IQ-carrier hull log-volume.
4. hScaling (every sourceScalingUnits log-degree <= 0) is substantive and not
   derived here.
5. q != 1 is NOT available from the current FiniteThetaPacket (only q_pos is
   stored). It is an explicit source input. Without it the Cor312ComparisonData
   field qParameter_log_ne_zero cannot be built.
6. The Cor312ComparisonData produced here is a value-layer surrogate; it must
   not be cited as paper xi-f. New paper-level tasks handle the actual q-pilot
   object, signed 1,circ U hull, O-module/vector-bundle layer, and paper
   inclusion.

No sorry/axiom/toy is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

open LeanFormal.IUT

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Value-layer normalized Theta-hull signed log-volume: source sup of
pointwise hull log-degrees divided by card(SourceVolumeIndex l). This is NOT the
paper 1,circ U hull volume. -/
def valueLayerThetaHullLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Real :=
  I.sourceThetaHullLogVolume v R n /
    (Fintype.card (SourceVolumeIndex l) : Real)

/-- Value-layer normalized inclusion, using the final XIF-1 normalized q-pilot
volume and the actual SourceXiFConstruction inclusion under hq/hScaling. -/
theorem valueLayerInclusion (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceNormalizedQPilotLogVolume v R n ≤
      I.valueLayerThetaHullLogVolume v R n := by
  unfold sourceNormalizedQPilotLogVolume valueLayerThetaHullLogVolume
  exact div_le_div_of_nonneg_right
    (I.sourceXiFInclusion v R n hq hScaling)
    (by exact_mod_cast le_of_lt (sourceVolumeIndex_card_pos l))

/-- Under q <= 1 and q != 1, the normalized q-pilot log-volume equals the paper
signed value -|log q|. This only recovers the sign; it does not identify the
paper q-pilot object. -/
theorem valueLayerQPilotLogVolume_eq_neg_abs_log (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hq_ne_one : (I.theaterAt 0 0).thetaPacket.q ≠ 1) :
    I.sourceNormalizedQPilotLogVolume v R n =
      -|Real.log ((I.theaterAt 0 0).thetaPacket.q)| := by
  rw [I.sourceNormalizedQPilotLogVolume_eq_log_q v R n]
  have hq_lt : (I.theaterAt 0 0).thetaPacket.q < 1 :=
    lt_of_le_of_ne hq hq_ne_one
  have hlog_neg : Real.log ((I.theaterAt 0 0).thetaPacket.q) < 0 :=
    Real.log_neg (I.theaterAt 0 0).thetaPacket.q_pos hq_lt
  rw [abs_of_neg hlog_neg, neg_neg]

/-- The q-parameter log is nonzero under q <= 1 and q != 1. -/
theorem valueLayerQParameter_log_ne_zero (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hq_ne_one : (I.theaterAt 0 0).thetaPacket.q ≠ 1) :
    Real.log ((I.theaterAt 0 0).thetaPacket.q) ≠ 0 := by
  have hq_lt : (I.theaterAt 0 0).thetaPacket.q < 1 :=
    lt_of_le_of_ne hq hq_ne_one
  exact ne_of_lt (Real.log_neg (I.theaterAt 0 0).thetaPacket.q_pos hq_lt)

/-- Value-layer Cor312ComparisonData. Surrogate: thetaHullLogVolume is the
value-layer normalized sup, qPilotLogVolume is the XIF-1 normalized source
value, and q != 1 is explicit. Do not cite as paper xi-f. -/
def valueLayerComparisonData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hq_ne_one : (I.theaterAt 0 0).thetaPacket.q ≠ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    Cor312ComparisonData where
  thetaHullLogVolume := I.valueLayerThetaHullLogVolume v R n
  qPilotLogVolume := I.sourceNormalizedQPilotLogVolume v R n
  qPilot_mem_ray := I.valueLayerInclusion v R n hq hScaling
  qParameter := (I.theaterAt 0 0).thetaPacket.q
  qParameter_pos := (I.theaterAt 0 0).thetaPacket.q_pos
  qParameter_log_ne_zero := I.valueLayerQParameter_log_ne_zero v R n hq hq_ne_one
  qPilotLogVolume_eq := I.valueLayerQPilotLogVolume_eq_neg_abs_log v R n hq hq_ne_one

/-- Numerical value-layer consequence, conditional on the same source
contraction hypotheses and explicit q != 1. Still not paper Cor3.12. -/
theorem valueLayerCor312CThetaLowerBound (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hq_ne_one : (I.theaterAt 0 0).thetaPacket.q ≠ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0)
    {cTheta : Real}
    (hc : I.valueLayerThetaHullLogVolume v R n ≤
      cTheta * |Real.log ((I.theaterAt 0 0).thetaPacket.q)|) :
    -1 ≤ cTheta := by
  let data := I.valueLayerComparisonData v R n hq hq_ne_one hScaling
  have hincl : -|Real.log data.qParameter| ≤ data.thetaHullLogVolume := by
    rw [← data.qPilotLogVolume_eq]
    exact data.qPilot_mem_ray
  have hc' : data.thetaHullLogVolume ≤
      cTheta * |Real.log data.qParameter| := by
    change I.valueLayerThetaHullLogVolume v R n ≤
      cTheta * |Real.log ((I.theaterAt 0 0).thetaPacket.q)|
    exact hc
  exact LeanFormal.IUT.cor312CThetaLowerBound data.qParameter_log_ne_zero hincl hc'

end OriginalInput
end Theorem311Source

end IUT
