/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A747: VcI explicit volume formulas and whether they give a hull lower bound -/

/- Inventory from Iut/WallEquiv/VcI.lean (repo-root Iut/; oleans not built here; read-only):
* `.md` intro l.20-32: `vcIPacket` components; `ssIneqNoHull_iff_packets` restates
  `SSIneqNoHull`; `logVol_hull_vcI_eq` for `hull(VC(I))` with `hullPacket`;
  `ssIneq_iff_packets` restates `SSIneq D` with this right-hand side;
  `logVol_hull_vcI_sub_eq` = average of weighted shell defects; `logVol_vcI_le_hull`;
* `hullPacket` (:689) and `packetVol_vcI` (:707); `hullPacket_sub_vcIPacket = defectPacket`
  (:725-726);
* at a prime: `vcIPacket_finite` = `sum_c w_c*(shellExcess + mu^log(R_I))`;
  `hullPacket_finite` = `sum_c w_c* sum_j rho_{c j}*log p` (exact);
* at a tame prime: `vcIPacket_tame`, `hullPacket_tame` = `sum_c w_c* sum_j (1 - 1/e_{c j})*log p`,
  `defectPacket_tame`, `defectPacket_tame_le`;
* `logVol_hull_vcI_eq` gives the hull log-volume as the procession average (`/l*`) of
  weighted packet hull sums; no lower-bound lemma for the total hull volume is present.

Verdict: the explicit formula is an EXACT expansion; a lower bound
`(s-1)*|log q| <= logVol(hull VC(I))` needs lower bounds for the weighted packet sums
(the `rho_{c j}` terms), which are the arithmetic local terms — not provided as lower
bounds in VcI.  The VcI identity plus `ssIneq_iff_packets` reduce `SSIneq` to the packet
inequality; that reduction is the precise remaining target. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1VcIVolumeFormulaAuditActual

/-- Formula rows: (object, shape, source). -/
def vcIFormulaRows : List (String × String × String) :=
  [ ("vcIPacket", "sum_c w_c*(shellExcess + mu^log(R_I)) (finite case)", "VcI.lean:vcIPacket_finite") ,
    ("hullPacket", "sum_c w_c* sum_j rho_{c j}*log p (exact)", "VcI.lean:hullPacket_finite") ,
    ("defect", "hullPacket - vcIPacket = defectPacket", "VcI.lean:725") ,
    ("hull logVolume", "(sum_i sum^fin hullPacket)/l*", "VcI.lean:logVol_hull_vcI_eq") ,
    ("SSIneq restated", "SSIneq D <=> packet inequality with hullPacket rhs", "VcI.lean:ssIneq_iff_packets") ,
    ("tame hullPipeline", "sum_c w_c* sum_j (1 - 1/e_{c j})*log p", "VcI.lean:hullPacket_tame") ]

theorem vcIFormulaRows_length : vcIFormulaRows.length = 6 := rfl

/-- The missing step in abstract form: a packet-sum lower bound feeds SSIneq via the
procession average (/l*) — this mirrors `ssIneq_iff_packets` without formalizing VcI. -/
theorem hullLower_of_packetSum {s absLogQ hullSum ellStar : ℝ} (hell : 0 < ellStar)
    (hpacket : (s - 1) * absLogQ * ellStar ≤ hullSum) :
    (s - 1) * absLogQ ≤ hullSum / ellStar := by
  rw [le_div_iff₀ hell]
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1VcIVolumeFormulaAuditActual
