import tmp.sheaf.xif.paper.Mzk1Stage4PaperComparisonRegionScalingDesignActual

/-! # Mzk1Stage4PaperRegionIdentityObstructionActual (stage4 lane; evidence, supplemental)

A622 module (stage4 supplementary evidence): with IDENTITY scaling the paper comparison
region is independent of the ABC triple, so triple-dependent scaling is necessary for
the height comparison.  The canonical mainline file is NOT modified.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual

universe u

/-- The identity-scaling region data: scale is the identity (no triple dependence). -/
def identityScaling (X : Type u) (unitRegion : Set X) (pt : X) :
    PaperComparisonRegionScaling X where
  scale := fun _ _ _ x => x
  unitRegion := unitRegion
  pt := fun _ _ _ => pt

/-- The identity-scaling region is just unit ∪ {pt}. -/
theorem identity_region_eq (X : Type u) (unitRegion : Set X) (pt : X)
    (a b c : Nat) :
    region (identityScaling X unitRegion pt) a b c = unitRegion ∪ {pt} := by
  simp [region, identityScaling]

/-- With identity scaling the comparison region does not depend on the triple. -/
theorem identity_region_independent (X : Type u) (unitRegion : Set X) (pt : X)
    (a b c a' b' c' : Nat) :
    region (identityScaling X unitRegion pt) a b c =
      region (identityScaling X unitRegion pt) a' b' c' :=
  by
  rw [identity_region_eq, identity_region_eq]
#check identityScaling
#check identity_region_independent
#check identity_region_eq

end LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual
end
