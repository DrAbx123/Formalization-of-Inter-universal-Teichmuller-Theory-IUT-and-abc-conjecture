import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual

/-! # S3131 paper-route FORWARD SKELETON (Cor 3.12 -> ABC, V2 interface)

Lead pivot: card P cannot be an input. This file gives the forward skeleton for the
paper-faithful route: field (a) of `Cor312EpsilonArithmeticComparisonV2`
(comparisonRegion/logShellPoint/membership) is CONSTRUCTED (singleton region around a
chosen point), while (b) height comparison and (c) region-volume vs normalized weight
are two EXPLICIT analytic residual families. `ABCConjecture` then follows from these
two families alone via the existing V2 bridge (card P is never assumed).

Honest status: (b) is the height/log-volume dictionary estimate (IUT IV Thm 1.10
shape); (c) is the IV section 2 / [GenEll] strength estimate. Neither is assumed
here as a theorem: they are the named residual fields of the data record.
No sorry/axiom/True/PUnit. -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual

universe u

/-- Forward residual data for the paper-faithful route: a choice of comparison points
plus the TWO analytic families that still have to be constructed for the actual hull
log-volume interface. (a) point/membership is built below from `point`.
Parameterization: instantiating `W` with the actual paper hull log-volume makes (b)
the hull V-form/canonical-readout input (MissingConcreteVFormCanonicalReadout) and (c)
the IV section 2 arithmetic-strength estimate. -/
structure PaperRouteResidualData {X : Type u} (W : IQHullLogVolumeInterface X) where
  point : Nat → Nat → Nat → X
  height_comparison :
    ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * (W.logVolume {point a b c}).toReal
  region_volume_bound :
    ∀ ε : Real, 0 < ε → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (W.logVolume {point a b c}).toReal ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D

/-- (a) Field construction: singleton comparison region, point membership by `simp`. -/
def comparisonOfResiduals {X : Type u} {W : IQHullLogVolumeInterface X}
    (R : PaperRouteResidualData W) (ε : Real) (hε : 0 < ε) :
    Cor312EpsilonArithmeticComparisonV2 W ε where
  comparisonRegion := fun a b c => {R.point a b c}
  logShellPoint := R.point
  logShellPoint_mem := by
    intro a b c
    exact Set.mem_singleton _
  height_le_comparisonRegionVolume := R.height_comparison ε hε
  regionVolume_le_normalizedWeight := R.region_volume_bound ε hε

/-- Assemble the V2 bridge interface from the forward residual data. -/
def bridgeOfResiduals {X : Type u} {W : IQHullLogVolumeInterface X}
    (R : PaperRouteResidualData W) : Cor312ToABCBridgeInterfaceV2 where
  carrier := X
  hullData := W
  epsilonComparison := fun ε hε => comparisonOfResiduals R ε hε

/-- **Paper-route conditional theorem:** ABC follows from the two analytic residual
families (b) height comparison and (c) region-volume strength, via the V2 bridge.
Card P is NOT a hypothesis. -/
theorem abcConjecture_of_paperRouteResiduals {X : Type u}
    {W : IQHullLogVolumeInterface X} (R : PaperRouteResidualData W) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjectureV2 (bridgeOfResiduals R)

#check PaperRouteResidualData
#check comparisonOfResiduals
#check bridgeOfResiduals
#check abcConjecture_of_paperRouteResiduals

end LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
end