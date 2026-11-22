/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual

/-!
# A524 hull-lane det readout vs the paper q reading (sign/normalization audit)

`detReadout x = -Real.log |x.q|`; the paper q-pilot reading is `-|log q|`
(`S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading`).  For `x.q ≥ 1`
they coincide; for `x.q < 1` the paper reading is `Real.log x.q = -detReadout x`
(sign flip).  The hull-lane `hcmp : packetDet * q ≤ 1` is equivalent to
`hullReadout ≤ detReadout` (the REVERSE of the paper direction); the paper direction
`paperQReading ≤ hullReadout` is equivalent to `1 ≤ packetDet * q` (proved below).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetPaperQSideActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]

/-- The paper q-pilot reading `-|log q|`. -/
def paperQReading (x : HullDetState label) : ℝ :=
  -|Real.log x.q|

/-- The hull readout is `log(packetDet packet)`. -/
theorem hullReadout_eq_log_packetDet (x : HullDetState label) :
    hullReadout x = Real.log (packetDet x.packet) := by
  unfold hullReadout
  exact packetLogVolume_eq_log_det x.packet

/-- For `q ≥ 1` the det readout IS the paper q reading. -/
theorem detReadout_eq_paperQReading_of_one_le (x : HullDetState label) (hq : 1 ≤ x.q) :
    detReadout x = paperQReading x := by
  unfold detReadout paperQReading
  rw [abs_of_pos x.q_pos, abs_of_nonneg (Real.log_nonneg hq)]

/-- For `q < 1` the paper reading is the NEGATIVE of the det readout. -/
theorem paperQReading_eq_neg_detReadout_of_lt_one (x : HullDetState label) (hq : x.q < 1) :
    paperQReading x = -detReadout x := by
  unfold detReadout paperQReading
  rw [abs_of_pos x.q_pos, abs_of_neg (Real.log_neg x.q_pos hq)]

/-- **Paper direction criterion**: `paperQReading x ≤ hullReadout x` iff
  `1 ≤ packetDet x.packet * x.q` (for `q ≥ 1`, where the readings agree). -/
theorem paper_criterion_of_one_le (x : HullDetState label) (hq : 1 ≤ x.q) :
    paperQReading x ≤ hullReadout x ↔ 1 ≤ packetDet x.packet * x.q := by
  have hP : 0 < packetDet x.packet :=
    packetDet_pos x.packet
  have hqpos : 0 < x.q := x.q_pos
  have hmul : 0 < packetDet x.packet * x.q := mul_pos hP hqpos
  unfold paperQReading
  rw [abs_of_nonneg (Real.log_nonneg hq)]
  rw [hullReadout_eq_log_packetDet]
  rw [show -Real.log x.q ≤ Real.log (packetDet x.packet) ↔
      0 ≤ Real.log (packetDet x.packet) + Real.log x.q by constructor <;> intro h <;> linarith]
  rw [← Real.log_mul hP.ne' hqpos.ne']
  exact Real.log_nonneg_iff (le_of_lt hmul)

/-- **Direction correction**: the hull-lane `hcmp : packetDet * q ≤ 1` is the REVERSE
  criterion (`hullReadout ≤ detReadout`), not the paper direction. -/
theorem hcmp_is_hull_le_det (x : HullDetState label) :
    hullReadout x ≤ detReadout x ↔ packetDet x.packet * x.q ≤ 1 :=
  hullReadout_le_detReadout_iff x

/-- Explicit witness: on the one-label packet `scale = 1/8`, `q = 2`, `hcmp` holds
  (`packetDet*q = 1/4 ≤ 1`) while the paper direction FAILS. -/
theorem paperDirection_fails_with_hcmp :
    ∃ x : HullDetState Unit,
      packetDet x.packet * x.q ≤ 1 ∧ ¬ (paperQReading x ≤ hullReadout x) := by
  classical
  refine ⟨{ packet := { scale := fun _ => (1 / 8 : ℝ), positive := fun _ => by norm_num },
            q := 2, q_pos := by norm_num,
            q_log_ne_zero := Real.log_pos (by norm_num : (1 : ℝ) < 2) |>.ne' }, ?_, ?_⟩
  · rw [show packetDet (label := Unit) (⟨fun _ => (1 / 8 : ℝ), fun _ => by norm_num⟩ :
        PositivePacket Unit) = 1 / 8 from by rw [packetDet_eq_prod]; simp]
    norm_num
  · intro hle
    have hcrit := (paper_criterion_of_one_le _ (by norm_num : (1 : ℝ) ≤ 2)).mp hle
    have hdet : packetDet (label := Unit) (⟨fun _ => (1 / 8 : ℝ), fun _ => by norm_num⟩ :
        PositivePacket Unit) = 1 / 8 := by rw [packetDet_eq_prod]; simp
    rw [hdet] at hcrit
    norm_num at hcrit

end LeanFormal.IUT.XiFPaper.Mzk1HullDetPaperQSideActual