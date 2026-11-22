/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QPilotR4Stage5AlignActual
import tmp.sheaf.xif.paper.Mzk1HullDetFourTriangleActual

/-!
# Mzk1QThetaHullDetAlignActual — q/Theta double-image readouts vs concrete hull/det readouts

A486/A487/A496 wiring: align the literal q-pilot / Theta-pilot readouts with the
concrete hull/det readouts of `Mzk1HullDetStep3115Actual` /
`Mzk1HullDetFourTriangleActual` (shared B-version `FourTriangleSynthesis`):

* `qThetaHullReadout = hullReadout ∘ qThetaState`;
* `qThetaDetReadout = detReadout ∘ qThetaState`;
* `qThetaState` is the literal `HullDetState` supplied by the double image (single
  q-norm scale at label 1, q-parameter `exp(-qThetaDetReadout)`);
* `qThetaReadout_ordered` is routed through the hull criterion
  `packetDet packet * q <= 1` and the concrete shared four-triangle wiring;
* the concrete SHE slot is the proved `SHEArrowStatement T`; `ipl`/`apt` are explicit
  named propositions with supplied evidence (no True placeholder).

No value-model carrier, no incomplete proof, no axiom. Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QThetaHullDetAlignActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetFourTriangleActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The positive hull packet of the literal double image: the q-norm scale at label 1
and unit scales elsewhere, so its log-volume is exactly `log ||q_V||`. -/
def qThetaPacket (b : Bad (nativePlaceSelection T)) :
    PositivePacket (SignedLabel l.value) where
  scale j := by
    classical
    exact if j = oneSignedLabel l then ‖(qVFamily T b).q‖ else 1
  positive j := by
    classical
    by_cases h : j = oneSignedLabel l
    · rw [if_pos h]
      exact qNorm_pos (qVFamily T b)
    · rw [if_neg h]
      norm_num

/-- The concrete hull/det state of the literal double image. -/
def qThetaState (b : Bad (nativePlaceSelection T)) :
    HullDetState (SignedLabel l.value) where
  packet := qThetaPacket T b
  q := Real.exp (-thetaPilotLogImage T b)
  q_pos := Real.exp_pos _
  q_log_ne_zero := by
    rw [Real.log_exp]
    exact ne_of_gt (neg_pos.mpr (thetaPilotLogImage_neg T b))

/-- The concrete hull readout of the q/Theta state is the signed q-pilot log-volume. -/
theorem hullReadout_qThetaState (b : Bad (nativePlaceSelection T)) :
    hullReadout (qThetaState T b) = qThetaHullReadout T b := by
  classical
  classical
  unfold hullReadout qThetaState
  rw [packetLogVolume]
  rw [Finset.sum_eq_single (oneSignedLabel l)]
  · simp [qThetaPacket, qThetaHullReadout, qPilotLogImage, localSignedLog]
  · intro j _ hne
    simp [qThetaPacket, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The concrete det readout of the q/Theta state is the signed Theta-pilot log-volume. -/
theorem detReadout_qThetaState (b : Bad (nativePlaceSelection T)) :
    detReadout (qThetaState T b) = qThetaDetReadout T b := by
  classical
  unfold detReadout qThetaState qThetaDetReadout
  rw [abs_of_pos (Real.exp_pos _)]
  rw [Real.log_exp]
  ring

/-- Composition form: `qThetaHullReadout = hullReadout ∘ qThetaState`. -/
theorem qThetaHullReadout_eq_hullReadout_comp :
    qThetaHullReadout T =
      (hullReadout (label := SignedLabel l.value)) ∘ qThetaState T := by
  funext b
  exact (hullReadout_qThetaState T b).symm

/-- Composition form: `qThetaDetReadout = detReadout ∘ qThetaState`. -/
theorem qThetaDetReadout_eq_detReadout_comp :
    qThetaDetReadout T =
      (detReadout (label := SignedLabel l.value)) ∘ qThetaState T := by
  funext b
  exact (detReadout_qThetaState T b).symm

/-- The q/Theta ordered comparison is equivalent to the hull criterion
`packetDet packet * q <= 1` (hull Step (xi-f) lemma on the literal state). -/
theorem qThetaReadout_ordered_iff_packetDet_mul_le_one
    (b : Bad (nativePlaceSelection T)) :
    qThetaHullReadout T b <= qThetaDetReadout T b ↔
      packetDet (qThetaPacket T b) * (qThetaState T b).q <= 1 := by
  classical
  have h := hullReadout_le_detReadout_iff (qThetaState T b)
  rw [hullReadout_qThetaState T b, detReadout_qThetaState T b] at h
  simpa [qThetaState] using h

/-- A486 main-chain hook: `qThetaReadout_ordered` gives the hull inequality
`packetDet packet * q <= 1` on the literal double-image state. -/
theorem qThetaPacketDet_mul_q_le_one (b : Bad (nativePlaceSelection T)) :
    packetDet (qThetaPacket T b) * (qThetaState T b).q <= 1 :=
  (qThetaReadout_ordered_iff_packetDet_mul_le_one T b).mp (qThetaReadout_ordered T b)

/-- Hull negativity for the concrete hull/det contract. -/
theorem hullReadout_qThetaState_neg (b : Bad (nativePlaceSelection T)) :
    hullReadout (qThetaState T b) < 0 := by
  classical
  classical
  rw [hullReadout_qThetaState T b]
  exact qPilotLogImage_neg T b

/-- Concrete shared hull/det four-triangle synthesis on the literal double-image state. -/
def qThetaHullDetSynthesis (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    FourTriangleSynthesis (HullDetState (SignedLabel l.value)) Unit :=
  hullDetFourTriangleConcrete (T := T) (qThetaState T b)
    (hullReadout_qThetaState_neg T b) ipl hipl apt hapt
    (qThetaPacketDet_mul_q_le_one T b)

/-- Cor 3.12 conclusion from the shared four-triangle synthesis of the double image. -/
theorem cor312Conclusion_qThetaHullDet (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (qThetaHullDetSynthesis T b ipl hipl apt hapt).contract :=
  cor312Conclusion_of_fourTriangleSynthesis _

#check qThetaHullReadout_eq_hullReadout_comp
#check qThetaDetReadout_eq_detReadout_comp
#check qThetaPacketDet_mul_q_le_one
#check cor312Conclusion_qThetaHullDet

end LeanFormal.IUT.XiFPaper.Mzk1QThetaHullDetAlignActual
end
