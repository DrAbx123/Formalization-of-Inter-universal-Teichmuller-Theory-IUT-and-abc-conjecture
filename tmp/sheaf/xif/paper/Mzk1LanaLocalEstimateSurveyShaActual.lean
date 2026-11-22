import Mathlib.Tactic

/-!
# shehdd A630 LANA IUT IV LocalEstimate survey/audit rows (Sha)

Machine-readable survey of lana_latest's `Iut.Concrete.LocalEstimate` (IUT IV
Steps (iv)-(vii); source file tmp/sheaf/lana_latest/Iut/Concrete/LocalEstimate.lean):
the seven `LocalEstimate` fields and their correspondence to our Gap1/Gap2 /
xi-e objects.  This audit file has no lana dependency, so it is green while the
lana module itself is still compiling.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1LanaLocalEstimateSurveyShaActual

structure LanaEstimateRow where
  field : String
  lanaSource : String
  gapCorrespondence : String
  status : String
  deriving Repr, DecidableEq

def lanaEstimateRows : List LanaEstimateRow :=
  [ ⟨"cont", "LocalEstimate.cont (line 461)", "container region per capsule/place", "GREEN_SOURCE"⟩
  , ⟨"cont_mem_hullRegions", "cont_mem_hullRegions (462)", "hull-region membership = xi-e containment source", "GREEN_SOURCE"⟩
  , ⟨"thetaPilot_subset", "thetaPilot_subset (463)", "Theta-pilot image inside container (Gap1 region source)", "GREEN_SOURCE"⟩
  , ⟨"cont_eq_integral", "cont_eq_integral (464)", "non-distinguished prime integral container (vol 0)", "GREEN_SOURCE"⟩
  , ⟨"vol_finite", "vol_finite (467)", "finite-place packet log-volume bound (Gap2/Step(v) source)", "GREEN_SOURCE"⟩
  , ⟨"vol_infinite", "vol_infinite (471)", "archimedean log-volume |I|*log(sqrt2*pi) (normalization)", "GREEN_SOURCE"⟩
  , ⟨"packetVol_mono", "packetVol_mono (475)", "volume monotonicity = Gap2 comparison source", "GREEN_SOURCE"⟩
  , ⟨"triple-dependent scale", "LocalEstimate.q_v^{j^2} scaling + weighted average", "Gap1 height comparison scale source", "NAMED_AUDIT"⟩
  , ⟨"capsuleBound", "(j+1)log(dK_p) - (j^2/2l)log q_p + ... (line 20)", "concrete Gap2 bound expression", "NAMED_AUDIT"⟩
  ]

theorem lanaEstimateRows_length : lanaEstimateRows.length = 9 := rfl

theorem lanaEstimateRows_statuses_ok :
    lanaEstimateRows.all (fun r =>
      r.status ∈ ["GREEN_SOURCE", "NAMED_AUDIT"]) = true := by
  decide

theorem lanaEstimateRows_has_vol_finite :
    lanaEstimateRows.any (fun r => r.field = "vol_finite") = true := by
  decide

theorem lanaEstimateRows_has_hull_membership :
    lanaEstimateRows.any (fun r => r.field = "cont_mem_hullRegions") = true := by
  decide

theorem lanaEstimateRows_has_packetVol_mono :
    lanaEstimateRows.any (fun r => r.field = "packetVol_mono") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1LanaLocalEstimateSurveyShaActual
