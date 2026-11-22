import tmp.sheaf.xif.paper.Mzk1FourTriangleSharedActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1HullDetStep3115Actual — concrete hull/det readouts for Step 3.11.5

A485/A487 (hull/det lane): concrete readouts on the shared B-version four-triangle
interface (`Mzk1FourTriangleSharedActual`):

* hullReadout x = packetLogVolume x.packet = finite hull log-volume log (packetDet packet);
* detReadout x = -log|q| = det-normalized q-pilot log-volume;
* Step (xi-f) comparison hullReadout <= detReadout <=> packetDet packet * q <= 1.

No sorry/axiom; no closure claim. Registry frozen 14041. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual

universe u

/-- Concrete state for the hull/det step: a positive packet (the hull data)
together with the q-parameter of the elliptic curve (q > 0, log q != 0). -/
structure HullDetState (label : Type u) [Fintype label] where
  /-- The positive packet whose log-volume is the hull log-volume. -/
  packet : PositivePacket label
  /-- The q-parameter of the elliptic curve. -/
  q : Real
  q_pos : 0 < q
  q_log_ne_zero : Real.log q ≠ 0

variable {label : Type u} [Fintype label] [DecidableEq label]

/-- Concrete hull readout: the frozen finite-packet log-volume of the hull. -/
def hullReadout (x : HullDetState label) : Real :=
  packetLogVolume x.packet

/-- Concrete det readout: the det-normalized q-pilot log-volume -log|q|. -/
def detReadout (x : HullDetState label) : Real :=
  - Real.log |x.q|

/-- The HDD decomposition with the concrete hull and det readouts (shared B version). -/
def hullDetHDD : HDDDecomp Real Real (HullDetState label) where
  hullReadout := hullReadout
  detReadout := detReadout

/-- The concrete dsc arrow: the single concrete state. -/
def hullDetDsc (x : HullDetState label) : Unit -> HullDetState label :=
  fun _ => x

/-- The concrete SHE output. -/
def hullDetSheOut : Unit := ()

/-- The hull readout is the finite hull log-volume log (packetDet packet). -/
theorem hullReadout_eq_log_hullVolume (x : HullDetState label) :
    hullReadout x = Real.log (packetDet x.packet) := by
  unfold hullReadout
  exact packetLogVolume_eq_log_det x.packet

/-- The hull readout is the matrix log-determinant readout of the packet diagonal matrix. -/
theorem hullReadout_eq_matrixLogDet (x : HullDetState label) :
    hullReadout x = matrixLogDet (packetDiagonalMatrix x.packet) := by
  unfold hullReadout
  exact packetLogVolume_eq_matrixLogDet x.packet

/-- The hull readout is the log of the product of the packet scales. -/
theorem hullReadout_eq_log_det_eq_prod (x : HullDetState label) :
    hullReadout x = Real.log (∏ i, x.packet.scale i) := by
  rw [hullReadout_eq_log_hullVolume, packetDet_eq_prod x.packet]

/-- The concrete det readout is -log q for the positive q-parameter. -/
theorem detReadout_eq_neg_log (x : HullDetState label) :
    detReadout x = - Real.log x.q := by
  unfold detReadout
  rw [abs_of_pos x.q_pos]

/-- The det readout is the log of the inverse q-parameter. -/
theorem detReadout_eq_log_inv (x : HullDetState label) :
    detReadout x = Real.log x.q⁻¹ := by
  rw [detReadout_eq_neg_log, ← Real.log_inv]

/-- Hull readout composed with dsc/SHE equals the hull log-volume. -/
theorem hullReadout_dsc_sheOut_eq_log_hullVolume (x : HullDetState label) :
    (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1 =
      Real.log (packetDet x.packet) := by
  show hullReadout x = Real.log (packetDet x.packet)
  exact hullReadout_eq_log_hullVolume x

/-- Det readout composed with dsc/SHE equals -log|q|. -/
theorem detReadout_dsc_sheOut_eq_neg_log_abs (x : HullDetState label) :
    (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2 =
      - Real.log |x.q| := rfl

/-- Det-normalized comparison criterion (Step (xi-f)). -/
theorem hullReadout_le_detReadout_iff (x : HullDetState label) :
    hullReadout x <= detReadout x ↔ packetDet x.packet * x.q <= 1 := by
  unfold hullReadout detReadout
  rw [packetLogVolume_eq_log_det, abs_of_pos x.q_pos, ← Real.log_inv]
  have hpos : 0 < packetDet x.packet := by
    rw [packetDet_eq_prod]
    exact Finset.prod_pos (fun i _ => x.packet.positive i)
  rw [Real.log_le_log_iff hpos (inv_pos.mpr x.q_pos)]
  rw [inv_eq_one_div, le_div_iff₀ x.q_pos]

/-- Step (xi-f) from the normalized inequality. -/
theorem hullReadout_le_detReadout_of_packetDet_mul_le_one
    (x : HullDetState label) (h : packetDet x.packet * x.q <= 1) :
    hullReadout x <= detReadout x :=
  (hullReadout_le_detReadout_iff x).mpr h

/-- The concrete Step 3.11.5 comparison for the shared four-triangle composite. -/
theorem step3115_comparison_hullDet (x : HullDetState label)
    (h : packetDet x.packet * x.q <= 1) :
    (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1 <=
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2 :=
  hullReadout_le_detReadout_of_packetDet_mul_le_one x h

/-- Rescaling the hull packet by c > 0 shifts the hull readout by card(label) * log c. -/
theorem hullReadout_rescale (x : HullDetState label) (c : Real) (hc : 0 < c) :
    hullReadout { x with packet := rescalePacket c hc x.packet } =
      (Fintype.card label : Real) * Real.log c + hullReadout x := by
  show packetLogVolume (rescalePacket c hc x.packet) =
    (Fintype.card label : Real) * Real.log c + packetLogVolume x.packet
  exact packetLogVolume_rescale c hc x.packet

/-- The log-volume of a tensor packet is the weighted sum. -/
theorem hullReadout_tensor {alpha beta : Type} [Fintype alpha] [Fintype beta]
    (p : PositivePacket alpha) (q : PositivePacket beta) :
    packetLogVolume (tensorPacket p q) =
      (Fintype.card beta : Real) * packetLogVolume p +
        (Fintype.card alpha : Real) * packetLogVolume q :=
  packetLogVolume_tensor p q

/-- Cor 3.12 conclusion from the concrete hull/det readouts (shared B four-triangle). -/
theorem cor312Conclusion_of_hullDetState (x : HullDetState label)
    (h : packetDet x.packet * x.q <= 1) (contract : StepXIContract)
    (hull_eq : contract.qSigned =
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1)
    (theta_eq : contract.thetaSigned =
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2) :
    Cor312Conclusion contract :=
  cor312Conclusion_of_fourTriangleSynthesis
    { contract := contract
      hdd := hullDetHDD
      dsc := hullDetDsc x
      sheOut := hullDetSheOut
      hull_eq := hull_eq
      theta_eq := theta_eq
      step3115_comparison := step3115_comparison_hullDet x h }

end LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
