import tmp.sheaf.xif.paper.Mzk1FourTriangleObjectActual

/-!
# A518 audit: four-triangle readouts vs paper Cor 3.12

## Objects audited (green `Mzk1HullDetStep3115Actual` / `Mzk1FourTriangleObjectActual`)

* `hullReadout x = packetLogVolume x.packet = Real.log (packetDet x.packet)`;
* `detReadout x = -Real.log |x.q|`;
* `hcmp : packetDet x.packet * x.q <= 1`, and
  `step3115_comparison_hullDet x hcmp : hullReadout x <= detReadout x`;
* in `FourTriangleSynthesis`: `contract.qSigned = readout.1 = hullReadout`,
  `contract.thetaSigned = readout.2 = detReadout`.

## ① Are these the paper `-|log Theta|` / `-|log q|`?  NO (only ad-hoc real readouts).

* `hullReadout = log (prod_i scale_i)` of an arbitrary `PositivePacket` (`scale > 0`
  only).  It has no theta values `q_v^{j^2}`, no `2*l`-th roots/Kummer, no
  possible-images union under (Ind1)(Ind2)(Ind3), no holomorphic hull, and no
  procession averaging over `j in F_l^x` / Haar normalization.  So it is not the
  paper `-|log Theta|` (procession-normalized log-volume of the hull).
* `detReadout = -log|x.q|` for an arbitrary `q > 0`.  The paper q-pilot is
  `-|log q| = -(1/(2l))*log(q)` with `log q` the normalized q-divisor degree
  ([IUTchIV] p.23, lines 1358-1363); for `0 < q < 1` our `detReadout` is
  `+|log q| > 0` (wrong sign), and in general the `1/(2l)` normalization is
  absent.  So it is not the paper `-|log q|` either.
* The contract slots are also **swapped**: paper `qSigned = -|log q|` and
  `thetaSigned = -|log Theta|`, while the current wiring assigns
  `qSigned = hullReadout` (Theta-hull side) and `thetaSigned = detReadout`
  (q side).  Thus `Cor312Conclusion` here is the ordered pair
  `hullReadout <= detReadout`, not the paper `-|log q| <= -|log Theta|`.

## ② Is `hcmp` derivable from the real theta/2l-root/Haar construction?  NO.

`Mzk1HullDetStep3115Actual.hullReadout_le_detReadout_iff` proves
`hullReadout x <= detReadout x  <->  packetDet x.packet * x.q <= 1`.
So `hcmp` is **definitionally equivalent to the comparison itself** (indeed to
its reversed direction, given the slot swap above).  It is an input assumption,
not a consequence of the packet/q data: `packet` and `q` are independent
abstract data with no relation to theta values, 2l-th roots or Haar measures.

## ③ Faithful comparison needed (not hcmp)

Construct/compare the actual paper objects:
* Theta side: theta values `{q_v^{j^2}}_{j=1..l*}` (l* = (l-1)/2), 2l-th roots in
  the Kummer extension (S342: no root in the completion itself), possible images
  under (Ind1)(Ind2)(Ind3), holomorphic hull, procession-normalized mono-analytic
  log-volume (average over `j in F_l^x`, sFactor = (l*+1)(2l*+1)/6) with the
  chosen Haar normalization; finite real number `-|log Theta|`;
* q side: the actual q-parameter data with `-|log q| = -(1/(2l))*log(q)`
  (normalized q-divisor degree, [IUTchIV] p.23);
* the comparison theorem `-|log q| <= -|log Theta|` derived from
  containment/(IPL,SHE,APT)/Step (xi-f) (or from C_Theta/hcomp in the ABC stage),
  with `qSigned = -|log q|`, `thetaSigned = -|log Theta|`.  `hcmp` must not be a
  field of the synthesis.

No sorry/axiom; this file only records the audit and the two sign/triviality
lemmas below.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleReadoutAuditA518

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]

/-- For `0 < q < 1`, `detReadout = -log q` is positive: it is `+|log q|`, not
the paper's negative `-|log q|`. -/
theorem audit_detReadout_pos_of_q_lt_one (x : HullDetState label) (hq : x.q < 1) :
    0 < detReadout x := by
  rw [detReadout_eq_neg_log]
  exact neg_pos.mpr (Real.log_neg x.q_pos hq)

/-- Under the natural q-parameter sign `q < 1` and `hullReadout < 0`, the
current Step 3.11.5 comparison `hullReadout <= detReadout` is automatic by
sign separation (no 3.12 content). -/
theorem audit_comparison_trivial_of_q_lt_one (x : HullDetState label)
    (hneg : hullReadout x < 0) (hq : x.q < 1) :
    hullReadout x <= detReadout x := by
  have hpos := audit_detReadout_pos_of_q_lt_one x hq
  linarith

/-- Conversely, with the paper slot assignment (`qSlot = detReadout`,
`thetaSlot = hullReadout`) the paper inequality `qSlot <= thetaSlot` is false
here whenever `hullReadout < 0` and `0 < q < 1`: the current comparison proves
the opposite direction. -/
theorem audit_paper_direction_fails_of_q_lt_one (x : HullDetState label)
    (hneg : hullReadout x < 0) (hq : x.q < 1) :
    ¬ detReadout x <= hullReadout x := by
  have hpos := audit_detReadout_pos_of_q_lt_one x hq
  linarith

/-- `hcmp` is exactly the current (reversed-slot) comparison, not a derivation
from real data. -/
theorem audit_hcmp_iff_comparison (x : HullDetState label) :
    hullReadout x <= detReadout x ↔ packetDet x.packet * x.q <= 1 :=
  hullReadout_le_detReadout_iff x

/-- The slot assignment in `FourTriangleSynthesis`: q/theta slots are
readouts 1/2, i.e. hull/det (swapped relative to the paper labels). -/
theorem audit_slot_assignment (O : FourTriangleObject label) :
    O.synthesis.contract.qSigned =
        (fourTriangleReadout O.synthesis.hdd O.synthesis.dsc O.synthesis.sheOut).1 ∧
      O.synthesis.contract.thetaSigned =
        (fourTriangleReadout O.synthesis.hdd O.synthesis.dsc O.synthesis.sheOut).2 :=
  ⟨O.synthesis.hull_eq, O.synthesis.theta_eq⟩

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleReadoutAuditA518
