/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import Mathlib.Tactic

/-! A518 AUDIT: HullDet readouts vs paper Cor 3.12 `-|log Theta|` / `-|log q|`.

FINDINGS (checked against the green Mzk1HullDetStep3115Actual):

(1) The two readouts are NOT the paper quantities as they stand:
  * `hullReadout x = packetLogVolume x.packet = Real.log (packetDet x.packet)`
    is a SIGNED log-det of an arbitrary positive finite packet: it can be
    positive or negative (no absolute value, no sign constraint). The paper
    quantity `-|log Theta|` is <= 0.
  * `detReadout x = -Real.log x.q` (since x.q > 0), while the paper q-pilot
    quantity is `-|log q|`; these agree only if `Real.log x.q >= 0` (q >= 1).
    For 0 < q < 1 our readout is positive while the paper quantity is negative.
  * No 2l/dimension normalization or literal Theta/q-pilot identification is
    present: the packet is an abstract PositivePacket, not the actual Theta-hull
    determinant data; detReadout is the det-normalized q reading, a different
    normalization from the literal Cor 3.12 Haar log-volume (cf. Prop 3.9(i)).

(2) `hcmp : packetDet x.packet * x.q <= 1` is exactly EQUIVALENT to the
comparison `hullReadout x <= detReadout x` (green theorem
`hullReadout_le_detReadout_iff`). It is therefore not an auxiliary
construction fact derivable from theta = q^{j^2}, the 2l-th root and the Haar
normalization: those constructions determine the DEFINITIONS of the two sides,
not their order. Assuming hcmp is assuming (a surrogate form of) the 3.12
inequality itself. It is also independent of `hneg` (hull negativity).

(3) The current four-triangle comparison is conditional on its conclusion:
`fourTriangleObject_comparison` consumes hcmp. To be faithful one needs
  * the literal q-pilot readout `qPilotLogVolumeReading P = -|log ||q|||`;
  * the literal Theta-hull Haar readout `thetaPilotHullLogVolumeReal C3`
    with the paper sign normalization `-|log Theta|`;
  * the actual determinant/packet object for the Theta hull (scales from the
    theta values q^{j^2/(2l)}, not an arbitrary packet) together with the
    Prop 3.9 (i) Haar normalization;
  * the honest target `qPilotLogVolumeReading P <= -|thetaPilotHullLogVolumeReal C3|`,
    to be derived from the Theorem 3.11 multiradial/possible-image route
    (xi-e containment + xi-f formal step), not from hcmp.

The lemmas below record (1) and (2) in Lean, plus the faithful target shape.
No comparison is asserted/proved here. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetReadoutAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]
variable {l : PrimeGeFive}

/-! ## 1. The readouts are signed raw log-volumes -/

theorem hullReadout_eq_logDet (x : HullDetState label) :
    hullReadout x = Real.log (packetDet x.packet) :=
  hullReadout_eq_log_hullVolume x

theorem detReadout_eq_neg_log_q (x : HullDetState label) :
    detReadout x = -Real.log x.q := detReadout_eq_neg_log x

/-- The paper q-pilot readout `-|log q|` as a function of the state. -/
def paperQPilotReadout (x : HullDetState label) : Real :=
  -|Real.log x.q|

theorem paperQPilotReadout_nonpos (x : HullDetState label) :
    paperQPilotReadout x <= 0 := neg_nonpos.mpr (abs_nonneg _)

/-- The det readout equals the paper q readout exactly on `log q >= 0`. -/
theorem detReadout_eq_paperQPilot_iff (x : HullDetState label) :
    detReadout x = paperQPilotReadout x <-> 0 <= Real.log x.q := by
  rw [detReadout_eq_neg_log_q, paperQPilotReadout]
  by_cases h : 0 <= Real.log x.q
  · rw [abs_of_nonneg h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · push_neg at h
    rw [abs_of_neg h]
    constructor
    · intro heq
      have hzero : Real.log x.q = 0 := by linarith
      linarith
    · intro hge
      linarith

/-- The paper Theta-pilot readout `-|log Theta|` from the signed hull readout. -/
def paperThetaHullReadout (x : HullDetState label) : Real :=
  -|hullReadout x|

theorem paperThetaHullReadout_nonpos (x : HullDetState label) :
    paperThetaHullReadout x <= 0 := neg_nonpos.mpr (abs_nonneg _)

/-! ## 2. hcmp is equivalent to the comparison -/

theorem hcmp_iff_hullReadout_le_detReadout (x : HullDetState label) :
    packetDet x.packet * x.q <= 1 <-> hullReadout x <= detReadout x :=
  (hullReadout_le_detReadout_iff x).symm

/-- The four-triangle comparison is exactly the hcmp input (not a consequence
of the packet/q construction). -/
theorem fourTriangleComparison_iff_hcmp (x : HullDetState label) :
    (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1 <=
        (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2 <->
      packetDet x.packet * x.q <= 1 := by
  show hullReadout x <= detReadout x <-> _
  exact hullReadout_le_detReadout_iff x

/-! ## 3. Concrete witnesses: hcmp is not determined by q alone -/

def unitPacket (s : Real) (hs : 0 < s) : PositivePacket Unit where
  scale := fun _ => s
  positive := fun _ => hs

theorem packetDet_unitPacket (s : Real) (hs : 0 < s) :
    packetDet (unitPacket s hs) = s := by
  rw [packetDet_eq_prod]
  simp [unitPacket]

def witnessState (s q : Real) (hs : 0 < s) (hq : 0 < q)
    (hlog : Real.log q ≠ 0) : HullDetState Unit where
  packet := unitPacket s hs
  q := q
  q_pos := hq
  q_log_ne_zero := hlog

/-- With q = 2: packet scale 1 gives hcmp false, packet scale 1/2 gives true. -/
theorem hcmp_false_witness :
    ¬ (packetDet (unitPacket 1 zero_lt_one) * 2 <= 1) := by
  rw [packetDet_unitPacket]
  norm_num

theorem hcmp_true_witness :
    packetDet (unitPacket (1/2) (by norm_num)) * 2 <= 1 := by
  rw [packetDet_unitPacket]
  norm_num

/-! ## 4. The faithful target shape (not proved here) -/

/-- The faithful Cor 3.12 comparison target on the actual C3 input: the paper
q-pilot readout is bounded by the sign-normalized actual Theta-hull readout. -/
def faithfulCor312Target {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Prop :=
  qPilotLogVolumeReading P <= -|thetaPilotHullLogVolumeReal C3|

theorem faithfulCor312Target_def {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    faithfulCor312Target C3 P <->
      qPilotLogVolumeReading P <= -|thetaPilotHullLogVolumeReal C3| := Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1HullDetReadoutAuditActual