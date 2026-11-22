/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1SSIneqVolumeActual
import Mathlib.Tactic

/-! # A901: can `avgDeg_gaussian` prove SSIneq?  Interface + precise gap -/

/- lana source facts (root Iut/ tree; oleans not built here):
* `Iut/ThetaLink/Gauss.lean:228 avgDeg_gaussian (q : L) :
   avgDeg (fun j : Fin n => q ^ ((j.1+1)^2)) = Wall.sFactor n * -Real.log ‖q‖`
  -- the Gaussian theta values `q^{j^2}` have average degree `sF * A` (`A = -log‖q‖`);
* `gaussLink` (:40), `linkEquiv_unique` (:199): the Theta-link is the identity on label 1
  and non-identity on other labels;
* `Iut/Wall/Ind3.lean:130 vcI_le_hullOf`: `VC(I) <= hull(VC(I))`;
  `exists_ind3_logVol_iff`: hull-adic log-volumes are `(-inf, logVol(hull)]`;
  `exists_le_vcI_logVol_iff`: adelic `S <= VC(I)` log-volumes are `<= logVol(VC(I))`.

WHAT IS MISSING: no lemma states `avgDeg(gaussGen) <= logVol(hull(vcI))`.  The hull is
taken over the CONTAINER `VC(I)` (log-shell tensors), not over the theta-pilot region;
the Gaussian values `q^{j^2}` are the norms in `avgDeg`, and no containment
`thetaPilotRegion <= hull(VC(I))` (or volume comparison with `avgDeg`) is proved in lana.
If such a comparison existed, SSIneq would follow IMMEDIATELY (since
`avgDeg = sF*A >= (sF-1)*A` for `A >= 0`), i.e. the route is equivalent-level, not new.

The interface below isolates the exact missing comparison. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqFromGaussActual

open LeanFormal.IUT.XiFPaper.Mzk1SSIneqVolumeActual

structure GaussHullComparison where
  sF : ℝ
  A : ℝ
  hullLogVol : ℝ
  gaussAvgDeg : ℝ
  avgDeg_eq : gaussAvgDeg = sF * A
  hull_ge_gauss : gaussAvgDeg ≤ hullLogVol

/-- **Interface-level SSIneq from the Gaussian comparison**: if the hull volume dominates
the Gaussian average degree `sF*A` and `0 <= A`, then `(sF-1)*A <= hullLogVol`. -/
theorem ssIneqForm_of_gaussComparison (G : GaussHullComparison) (hA : 0 ≤ G.A) :
    SSIneqForm G.sF G.A G.hullLogVol := by
  unfold SSIneqForm
  have h := G.hull_ge_gauss
  rw [G.avgDeg_eq] at h
  nlinarith

def gaussRows : List (String × String × String) :=
  [ ("avgDeg_gaussian", "Iut/ThetaLink/Gauss.lean:228", "LANA (olean needed)") ,
    ("gaussLink / linkEquiv_unique", "Gauss.lean:40/199", "LANA (olean needed)") ,
    ("vcI_le_hullOf", "Iut/Wall/Ind3.lean:130", "LANA (olean needed)") ,
    ("gaussAvgDeg = sF*A", "field avgDeg_eq", "INTERFACE FIELD") ,
    ("hullLogVol >= gaussAvgDeg", "NEEDED comparison: theta region vs hull(VC(I))", "MISSING (no lana lemma)") ,
    ("ssIneqForm_of_gaussComparison", "comparison + 0<=A => (sF-1)A <= hullLog", "PROVED (arithmetic)") ]

theorem gaussRows_length : gaussRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqFromGaussActual
