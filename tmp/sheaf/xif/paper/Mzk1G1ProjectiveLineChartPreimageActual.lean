import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import tmp.sheaf.xif.paper.Mzk1SchemeOpensRangeInterfaceActual
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual

/-- For a gluing data D, the preimage of the j-chart under the i-chart inclusion is the
image of the (i,j)-overlap: the two charts meet exactly along the overlap. -/
theorem preimage_opensRange_ι {D : Scheme.GlueData} (i j : D.J) :
    (D.ι i) ⁻¹ᵁ (D.ι j).opensRange = (D.f i j).opensRange := by
  ext x
  haveI : IsOpenImmersion (D.f i j) := D.f_open i j
  change (D.ι i) x ∈ (D.ι j).opensRange ↔ x ∈ (D.f i j).opensRange
  rw [Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · rintro ⟨y, hy⟩
    have hrel : D.Rel ⟨i, x⟩ ⟨j, y⟩ := (D.ι_eq_iff i j x y).mp hy.symm
    obtain ⟨z, hz, -⟩ := hrel
    exact ⟨z, hz⟩
  · rintro ⟨z, hzx⟩
    refine ⟨(D.t i j ≫ D.f j i) z, ?_⟩
    have hrel : D.Rel ⟨i, x⟩ ⟨j, (D.t i j ≫ D.f j i) z⟩ := ⟨z, hzx, rfl⟩
    exact ((D.ι_eq_iff i j x _).mpr hrel).symm

/-- The t-chart preimage of the lambda chart is the overlap (as an open of the t-chart). -/
theorem localChartInf_preimage_localChart0 :
    localChartInf ⁻¹ᵁ localChart0.opensRange = overlapToChartInf.opensRange := by
  have h := preimage_opensRange_ι (D := p1GlueData) (ULift.up true) (ULift.up false)
  show (p1GlueData.ι (ULift.up true)) ⁻¹ᵁ (p1GlueData.ι (ULift.up false)).opensRange =
    overlapToChartInf.opensRange
  rw [h]
  rfl

/-- The lambda-chart preimage of the t-chart is the overlap (as an open of the
lambda-chart). -/
theorem localChart0_preimage_localChartInf :
    localChart0 ⁻¹ᵁ localChartInf.opensRange = overlapToChart0.opensRange := by
  have h := preimage_opensRange_ι (D := p1GlueData) (ULift.up false) (ULift.up true)
  show (p1GlueData.ι (ULift.up false)) ⁻¹ᵁ (p1GlueData.ι (ULift.up true)).opensRange =
    overlapToChart0.opensRange
  rw [h]
  rfl

/-- The two charts of P^1 cover it: their open images have supremum top. -/
theorem localChart0_opensRange_sup_localChartInf :
    localChart0.opensRange ⊔ localChartInf.opensRange = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
    Set.mem_univ, iff_true]
  simpa [Scheme.Hom.mem_opensRange, Set.mem_range] using localChart_jointly_surjective x

#print axioms preimage_opensRange_ι
#print axioms localChartInf_preimage_localChart0
#print axioms localChart0_preimage_localChartInf
#print axioms localChart0_opensRange_sup_localChartInf
end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
