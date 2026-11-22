/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FourTriangleObjectActual
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.Mzk1HullDetFourTriangleActual

/-!
# A518 audit: the four-triangle comparison `step3115_comparison_hullDet` (NOT a 3.12 proof)

## ① Sign / normalization of the two readouts

* `hullReadout x = packetLogVolume x.packet = Real.log (packetDet x.packet)`
  (`Volume.lean:32,44`; `packetDet = ∏ i, packet.scale i`, `scale i > 0`).
* `detReadout x = - Real.log |x.q|` (`Mzk1HullDetStep3115Actual.lean`).
* Under `x.q > 0` (`x.q_pos`), `detReadout x = - Real.log x.q`, which is the paper's
  `-|log q|` (paper: IUT III Cor 3.12, lines 10339-10353; the q-side reading is
  `-|log q| < 0`). So the SIGN convention is consistent for the det side.
* The hull side `log(packetDet)` has NO built-in sign/procession normalization: a
  `PositivePacket` is arbitrary positive data and `packetLogVolume` can be any real
  number. The paper's `-|log(Theta)|` is the procession-normalized mono-analytic
  log-volume of the HOLOMORPHIC HULL of the union of possible images of the
  Theta-pilot object (paper lines 10329-10338), i.e. a finite, negative-real quantity
  whose value is computed from the theta values `q^{j^2}`, the 2l-th roots, the hull
  and the Haar/procession normalization.  The hull-lane `packetLogVolume` is the
  frozen finite-packet log-volume of an ARBITRARY packet; it is NOT identified with
  the paper hull log-volume anywhere.  Hence: sign convention OK on the det side,
  NOT established on the hull side; no procession average (sFactor) and no theta
  values enter the def.

## ② Is `hcmp : packetDet packet * q <= 1` derivable from the real construction?

* `hcmp` is *exactly equivalent* to `hullReadout x <= detReadout x`
  (`hullReadout_le_detReadout_iff`, reproved below as
  `comparison_iff_packetDet_mul_q_le_one`).  Therefore `hcmp` IS the 3.12 (xi-f)
  comparison itself (paper Step (xi-f), lines 10888-10898), not a consequence of the
  theta-value/2l-root/Haar construction: deriving it from that construction is the
  content of IUT III Theorem 3.11 + Cor 3.12.
* It is moreover NOT derivable from the data in `HullDetState`: the packet and q are
  independent parameters.  `comparison_not_automatic` constructs a state with
  `packetDet packet * q > 1` (hence the comparison FAILS), so no proof can exist
  without an extra input.

## ③ Faithfulness verdict and required objects

* `Mzk1FourTriangleObjectActual.fourTriangleObject_comparison` is only the formal
  implication `hcmp -> hullReadout <= detReadout`; it is a RE-EXPRESSION of the
  comparison, not a proof of it.  Its Cor 3.12 conclusion is conditional on `hcmp`.
* To make it faithful one must identify
  (i) `hullReadout` with the literal `-|log(Theta)|`: the procession-averaged
      (sFactor/`globalThetaLogVolume_average`) log-volume of the holomorphic hull of the
      actual tensor log-shell region (`S3137ThetaHullVolumeScalingActual`,
      `AbsTopIII09ThetaHullScalingActual`, `Mzk1Thm311LogShellActual` container/log-shell),
      including the theta values `thetaValueMon qroot j = qroot^{j^2}` and `qroot^{2l}=q`
      (`O2ThetaObjectActual`), and
  (ii) `detReadout` with the literal `-|log q|` of the actual q-pilot object
      (`Mzk1QPilotSHEDoubleImageActual.qPilotLogImage`, `HullDetObjectActual.qPilotLogVolume`),
  and then prove the comparison from the multiradial algorithm's possible-image/hull
  data (`MRRep.possibleRegion` together with the (Ind3) closure
  `MRRep.subset_possibleRegion`, `RefLANAMultiradialSpecActual`; xi-e containment).
* Until then the four-triangle comparison must be treated as an explicit named gap
  (`hcmp`), not as a 3.12 proof; the q/(2l) chain remains VOID.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]

/-- The det readout is `-log|q|` (definitional). -/
theorem detReadout_eq_neg_log_abs (x : HullDetState label) :
    detReadout x = - Real.log |x.q| := rfl

/-- Under `q > 0` the det readout is the paper's `-|log q| = -log q`. -/
theorem detReadout_eq_neg_log_of_pos (x : HullDetState label) :
    detReadout x = - Real.log x.q := by
  rw [detReadout_eq_neg_log_abs, abs_of_pos x.q_pos]

/-- The hull readout is `log(packetDet packet)`. -/
theorem hullReadout_eq_log_packetDet (x : HullDetState label) :
    hullReadout x = Real.log (packetDet x.packet) := by
  unfold hullReadout
  exact packetLogVolume_eq_log_det x.packet

/-- **The four-triangle comparison is exactly the input condition** `packetDet * q <= 1`;
  it is the (xi-f) comparison itself, not a consequence of the theta/2l/Haar data. -/
theorem comparison_iff_packetDet_mul_q_le_one (x : HullDetState label) :
    hullReadout x <= detReadout x ↔ packetDet x.packet * x.q <= 1 :=
  hullReadout_le_detReadout_iff x

/-- **The comparison is not automatic**: a concrete state on the one-label packet with
  `scale = 2`, `q = 2` has `packetDet * q = 4 > 1`, i.e. the comparison FAILS.  Hence
  no proof of the comparison can exist from `HullDetState` alone. -/
theorem comparison_not_automatic :
    ∃ x : HullDetState Unit,
      ¬ (hullReadout x <= detReadout x) := by
  classical
  refine ⟨{ packet := { scale := fun _ => 2, positive := fun _ => by norm_num },
            q := 2, q_pos := by norm_num,
            q_log_ne_zero := Real.log_pos (by norm_num : (1 : Real) < 2) |>.ne' }, ?_⟩
  rw [comparison_iff_packetDet_mul_q_le_one]
  have hdet : packetDet (label := Unit) (⟨fun _ => 2, fun _ => by norm_num⟩ :
      PositivePacket Unit) = 2 := by
    rw [packetDet_eq_prod]
    simp
  rw [hdet]
  norm_num

/-- Summary: the four-triangle object's comparison output is a restatement of its
  `hcmp` field, so `fourTriangleObject_cor312` is conditional on the (xi-f) comparison
  and cannot be cited as an unconditional 3.12 proof. -/
theorem fourTriangleObject_comparison_is_hcmp (x : HullDetState label)
    (hcmp : packetDet x.packet * x.q <= 1) :
    hullReadout x <= detReadout x ↔ packetDet x.packet * x.q <= 1 :=
  comparison_iff_packetDet_mul_q_le_one x

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleAuditActual