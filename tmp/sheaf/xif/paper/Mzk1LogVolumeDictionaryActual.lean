/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A760: log-volume dictionary — lana per-place formulas vs our hull formula -/

/- lana side (repo-root Iut/, read-only):
* `logVol U = (LocalTheory.vol D.placeSect (nC D)).processionVol U` (Wall/Rss.lean:324),
  i.e. logVol = (1/nC)*sum_i globalVol_i (procession average over the nC capsules);
* packet term: `hullPacket i vQ = sum_c w_c * componentVol leastHull(vcIComp)`
  (WallEquiv/VcI.lean:689-693), with `logVol_hull_vcI_eq` (VcI:740+) =
  `(sum_i sum^fin hullPacket i vQ)/nC`;
* finite place (exact): `componentVol leastHull(tensorLogShell) = sum_j rho_{c j} * log p`
  (`componentVol_leastHull_tensorLogShell_eq`, VcI doc l.50-55), rho_w = logShellRadius,
  I_w <= p^{-rho_w} O_w sharply; weighted form `hullPacket_finite =
  sum_c w_c * sum_j rho_{c j} * log p`;
* archimedean place: `vcIDefect` at infinity is `archDefect` (VcI:700); the archimedean
  log-volume involves `Real.log (Real.sqrt 2 * Real.pi)` (VcI:657), so the archimedean
  contribution is a `log(sqrt 2 * pi)`-type constant per component, not zero.

our side (hull green Mzk1HullLogVolumeFormulaActual):
* productHaar hull = prod_b mu_b(closedBall 0 rootImageRadius_b);
* normalizedLog hull = sum_b (log mu_ball_b - log mu_unit_b)  (no archimedean, no procession
  average, no 1/nC);
* s1902LogVolume hull = ofReal (1 + normalizedLog hull), unitRegion volume = 1.

Bridge requirements (the precise missing items):
(1) per-finite-place: our `sum_b d_b log q_b` (= lan QPilotData.logQ) versus lana packet sum
    `sum_c w_c sum_j rho_{c j} log p` — needs the normalized-weight dictionary
    d_b = f_b/[F:Q] and rho_{c j} = -log_p(rootImageRadius) identification;
(2) archimedean: our ball log-volume has no `log(sqrt 2 * pi)` term, lana hull includes
    archDefect-type archimedean contributions per capsule (VcI:657,700);
(3) procession average: lana divides by nC (and by 2l for absLogQ); our normalizedLog is
    NOT divided by nC;
(4) constant: our s1902LogVolume adds +1 relative to unit region (green S1902).
If (1)-(4) are supplied, the arithmetic bridge below turns our stronger geometric inequality
into lana SSIneq. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeDictionaryActual

/-- **Bridge skeleton**: if the geometric chain gives `logQ <= ourHullLog` (coefficient 1),
and our hull log-volume is at most lana's `hullLogLana`, and `0 <= c <= 1`, `0 <= logQ`,
then lana's coefficient form holds: `c*logQ <= hullLogLana`. -/
theorem ssIneq_of_logVolume_bridge {c logQ ourHullLog hullLogLana : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : 0 ≤ logQ)
    (hgeom : logQ ≤ ourHullLog) (hvol : ourHullLog ≤ hullLogLana) :
    c * logQ ≤ hullLogLana := by
  nlinarith

/-- Dictionary rows: (side, object, formula, source). -/
def logVolumeDictionaryRows : List (String × String × String × String) :=
  [ ("lana", "logVol", "(1/nC)*sum_i globalVol_i (processionVol)", "Wall/Rss.lean:324") ,
    ("lana", "hullPacket", "sum_c w_c * componentVol leastHull(vcIComp)", "VcI.lean:689") ,
    ("lana", "finite leastHull", "sum_j rho_{c j}*log p", "VcI.lean:componentVol_leastHull_tensorLogShell_eq") ,
    ("lana", "archimedean", "archDefect, log(sqrt 2 * pi) terms", "VcI.lean:657,700") ,
    ("ours", "normalizedLog hull", "sum_b (log mu_ball_b - log mu_unit_b)", "Mzk1HullLogVolumeFormulaActual") ,
    ("ours", "unit region", "volume = 1", "S1902") ]

theorem logVolumeDictionaryRows_length : logVolumeDictionaryRows.length = 6 := rfl

/-- lana coefficient `c_lana = (sFactor(nC)-1)/(2*l)` in terms of nC and l, given the
sum-of-squares evaluation `sFactor nC = (nC+1)(2nC+1)/6`. -/
theorem lana_coeff_form {nC l : ℝ} (hl : l = 2 * nC + 1)
    (hs : (nC + 1) * (2 * nC + 1) / 6 = (nC + 1) * (2 * nC + 1) / 6) :
    (((nC + 1) * (2 * nC + 1) / 6) - 1) / (2 * l) =
      ((nC + 1) * (2 * nC + 1) - 6) / (12 * (2 * nC + 1)) := by
  rw [hl]
  field_simp
  ring

/-- our theta-radius exponent: with theta_j = root^{j^2} and root^{2l} = q, the leading
exponent is `nC^2/(2l)` (max at j = nC), so `log rootImageRadius = -(nC^2/(2l))·logQ`-shape. -/
def ourCoeff (nC l : ℝ) : ℝ := nC ^ 2 / (2 * l)

/-- At l = 13 (nC = 6): our coefficient `36/26 = 18/13`; lana coefficient `85/156`;
ratio = `(18/13)/(85/156) = 156*18/(13*85) = 216/85`. -/
theorem coeff_compare_l13 :
    ((36 : ℝ) / 26) / (85 / 156) = 216 / 85 := by
  norm_num

/-- The bridge coefficient inequality `c_lana <= c_our` (needed for the volume bridge to
imply SSIneq from the stronger geometric inequality): `85/156 <= 18/13`. -/
theorem lana_coeff_le_our_l13 : (85 : ℝ) / 156 ≤ 18 / 13 := by
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeDictionaryActual
