import tmp.sheaf.xif.paper.Mzk1TreeR9HullRayActual
import tmp.sheaf.xif.paper.Mzk1TreeDownRayLatticeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ChainHullRayLatticeActualAdapted (adapted copy, A475 reuse) — A475 chained adapters: hull ray lattice

Chains the donor ray-identification theorem
(`Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay`) with the down-ray lattice
laws (`Mzk1TreeDownRayLatticeActual.downRay_inter/downRay_union/downRay_mono`)
to obtain the lattice laws directly for the H5 hull log-volume ray.
No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainHullRayLatticeActualAdapted

open LeanFormal.IUT

/-- Chain: H5 hull ray intersection = hull ray at min. -/
theorem chain_hullRay_inter (a b : ℝ) :
    hullLogVolumeRay a ∩ hullLogVolumeRay b = hullLogVolumeRay (min a b) := by
  rw [LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay,
    LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay,
    LeanFormal.IUT.XiFPaper.Mzk1TreeDownRayLatticeActual.downRay_inter,
    LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay]

/-- Chain: H5 hull ray union = hull ray at max. -/
theorem chain_hullRay_union (a b : ℝ) :
    hullLogVolumeRay a ∪ hullLogVolumeRay b = hullLogVolumeRay (max a b) := by
  rw [LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay,
    LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay,
    LeanFormal.IUT.XiFPaper.Mzk1TreeDownRayLatticeActual.downRay_union,
    LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay]

/-- Chain: H5 hull ray threshold monotonicity. -/
theorem chain_hullRay_mono {a b : ℝ} (h : a ≤ b) :
    hullLogVolumeRay a ⊆ hullLogVolumeRay b := by
  rw [LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay,
    LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay]
  exact LeanFormal.IUT.XiFPaper.Mzk1TreeDownRayLatticeActual.downRay_mono h

def chainHullRayRows : List (String × String × String) :=
  [ ("hull ray intersection", "CHAIN PROVED", "chain_hullRay_inter"),
    ("hull ray union", "CHAIN PROVED", "chain_hullRay_union"),
    ("hull ray monotonicity", "CHAIN PROVED", "chain_hullRay_mono") ]

theorem chainHullRayRows_length : chainHullRayRows.length = 3 := rfl

#check chain_hullRay_union
#check chainHullRayRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ChainHullRayLatticeActualAdapted
end