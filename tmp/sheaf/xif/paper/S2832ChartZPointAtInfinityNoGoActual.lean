import tmp.sheaf.xif.paper.S2831E37InfinityNotOverlapActual
import tmp.sheaf.xif.paper.S2829E37GaussianPointActual
import tmp.sheaf.xif.paper.S2801D6FaithfulActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2832ChartZPointAtInfinityNoGoActual

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual
open LeanFormal.IUT.XiFPaper.S2829E37GaussianPointActual

/-- The actual morphism from the base point to the point at infinity, through
the chart-Y infinity section. -/
noncomputable def S2832PointAtInfinityMorphism :
    Spec (CommRingCat.of K) ⟶ S2820E37ProjectiveScheme K :=
  (S2829ChartYInfinityOver).left ≫ S2820E37ChartYMap K

/-- The point at infinity is not in the image of the chart-Z open immersion:
no base morphism to the affine chart Z maps to it. -/
theorem S2832_no_chartZ_map_to_pointAtInfinity :
    ¬ ∃ z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
        z ≫ S2820E37ChartZMap K = S2832PointAtInfinityMorphism := by
  rintro ⟨z, hz⟩
  let D : Scheme.GlueData.{0} := E37ProjGlueData K (S2820E37TransitionIso K)
  let p : Spec (CommRingCat.of K) := default
  have hinf : (S2829ChartYInfinityOver).left p = E37InfinityPoint K := by
    change PrimeSpectrum.comap (E37InfinityEval K) p = E37InfinityPoint K
    rfl
  have hzpoint := congrArg (fun f => f p) hz
  have hzpoint' : D.ι (ULift.up false) (z p) =
      D.ι (ULift.up true) ((Over.Hom.left S2829ChartYInfinityOver) p) := by
    exact hzpoint
  rw [hinf] at hzpoint'
  have hz' : D.ι (ULift.up false) (z p) =
      D.ι (ULift.up true) (E37InfinityPoint K) := hzpoint'
  have hrel := (Scheme.GlueData.ι_eq_iff D (ULift.up false) (ULift.up true)
    (z p) (E37InfinityPoint K)).mp hz'
  rcases hrel with ⟨x, hxleft, hxright⟩
  apply S2831_infinityPoint_not_mem_overlap_range K
  refine ⟨(S2820E37TransitionIso K).hom x, ?_⟩
  have hxright' : E37ChartYOverlapMap K ((S2820E37TransitionIso K).hom x) =
      E37InfinityPoint K := by
    simpa [D, E37ProjGlueData, E37ProjT, E37ProjF, E37ProjV] using hxright
  exact hxright'

#check S2832PointAtInfinityMorphism
#check S2832_no_chartZ_map_to_pointAtInfinity
#print axioms S2832_no_chartZ_map_to_pointAtInfinity

end LeanFormal.IUT.XiFPaper.S2832ChartZPointAtInfinityNoGoActual
end
