import tmp.sheaf.xif.paper.S3068OpenImmersionFactorizationActual
import tmp.sheaf.xif.paper.S3067PointRealizationActual
import tmp.sheaf.xif.paper.S2831E37InfinityNotOverlapActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3068OpenImmersionFactorizationActual
open LeanFormal.IUT.XiFPaper.S3067PointRealizationActual
open LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3069RangeInclusionActual

/-- The infinity point in the S3068 glued scheme. -/
noncomputable def S3069Infinity : D.glued :=
  D.ι (ULift.up true) (E37InfinityPoint S2844D6F6BaseChangeActual.K)

/-- No chart-Z point maps to infinity. -/
theorem S3069_chartZ_ne_infinity
    (y : S2801E37AffineScheme S2844D6F6BaseChangeActual.K) :
    ChartZ y ≠ S3069Infinity := by
  intro h
  change D.ι (ULift.up false) y = D.ι (ULift.up true)
    (E37InfinityPoint S2844D6F6BaseChangeActual.K) at h
  rw [Scheme.GlueData.ι_eq_iff] at h
  rcases h with ⟨v, _hvleft, hvright⟩
  apply S2831_infinityPoint_not_mem_overlap_range S2844D6F6BaseChangeActual.K
  refine ⟨S3068OpenImmersionFactorizationActual.e.hom v, ?_⟩
  change (E37ChartYOverlapMap S2844D6F6BaseChangeActual.K)
    ((S2820E37TransitionIso S2844D6F6BaseChangeActual.K).hom v) =
      E37InfinityPoint S2844D6F6BaseChangeActual.K at hvright
  exact hvright

/-- Exact βs point data needed for range inclusion. -/
def S3069BetaPointData (βs : D.glued ⟶ D.glued) : Prop :=
  Function.Injective βs ∧ βs S3069Infinity = S3069Infinity

/-- Actual range inclusion from the point data. -/
theorem S3069_rangeInclusion_of_data
    (βs : D.glued ⟶ D.glued)
    (hdata : S3069BetaPointData βs)
    (hnon : ∀ x : D.glued, x ≠ S3069Infinity → βs x ≠ S3069Infinity) :
    Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ := by
  rintro y ⟨x, hx⟩
  subst y
  change βs (ChartZ x) ∈ Set.range ChartZ
  by_contra hnot
  have hyinf : βs (ChartZ x) = S3069Infinity := by
    by_contra hne
    rcases S3067_pointRealization (βs (ChartZ x)) hne with ⟨z, hz⟩
    exact hnot ⟨z, hz⟩
  have hxinf : ChartZ x = S3069Infinity :=
    hdata.1 (by rw [hyinf, hdata.2])
  exact S3069_chartZ_ne_infinity x hxinf

theorem S3069_betaPointData_of_square
    (βs : D.glued ⟶ D.glued)
    (hsq : βs ≫ βs = 𝟙 D.glued)
    (hnon : ∀ x : D.glued, x ≠ S3069Infinity → βs x ≠ S3069Infinity) :
    S3069BetaPointData βs := by
  have hsq_point : ∀ x : D.glued, βs (βs x) = x := by
    intro x
    have h := congrArg (fun f : D.glued ⟶ D.glued => f x) hsq
    simpa using h
  constructor
  · intro x y hxy
    have h := congrArg βs hxy
    rwa [hsq_point x, hsq_point y] at h
  · by_contra hne
    have h1 : βs (βs S3069Infinity) ≠ S3069Infinity :=
      hnon (βs S3069Infinity) hne
    exact h1 (hsq_point S3069Infinity)

theorem S3069_rangeInclusion_of_beta
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (βs : D.glued ⟶ D.glued)
    (hβs : βs = β.left)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hnon : ∀ x : D.glued, x ≠ S3069Infinity → βs x ≠ S3069Infinity) :
    Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ := by
  have hsq : βs ≫ βs = 𝟙 D.glued := by
    have h := congrArg (fun f => Over.Hom.left f) hβ
    change Over.Hom.left β ≫ Over.Hom.left β =
      𝟙 (S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K) at h
    rw [← hβs] at h
    exact h
  exact S3069_rangeInclusion_of_data βs
    (S3069_betaPointData_of_square βs hsq hnon) hnon

/-- From the range inclusion and hβs, obtain S3062ChartZFactorization β. -/
theorem S3069_factorization_of_range
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (βs : D.glued ⟶ D.glued)
    (hβs : βs = β.left)
    (H : Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ) :
    S3062ChartZFactorization β := by
  refine ⟨S3068_lift βs H, ?_⟩
  rw [← hβs]
  exact S3068_lift_fac βs H

/-!
## Exact statements and first error

Actual:
* S3069Infinity: the D-side infinity point.
* S3069_chartZ_ne_infinity: no chart-Z point maps to infinity, via
  GlueData.ι_eq_iff and S2831_infinityPoint_not_mem_overlap_range.
* S3069_rangeInclusion_of_data: if βs is point-injective, fixes infinity, and
  maps non-infinity points to non-infinity points, then
  Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ, using S3067_pointRealization.

First error:
S3069BetaPointData βs is not constructed from β order two and
hβs : βs = β.left.  Required:
* βs ≫ βs = 𝟙 D.glued from β ≫ β = 𝟙 and hβs;
* point injectivity from βs²=id;
* βs(∞)=∞ from the non-infinity condition and βs²=id.
These point-map/injectivity packages are not formalized.  No range inclusion
is faked.
-/

#check S3069Infinity
#check S3069_chartZ_ne_infinity
#check S3069_betaPointData_of_square
#check S3069_rangeInclusion_of_beta
#check S3069BetaPointData
#check S3069_factorization_of_range
#check S3069_rangeInclusion_of_data
#print axioms S3069_chartZ_ne_infinity
#print axioms S3069_betaPointData_of_square
#print axioms S3069_rangeInclusion_of_beta
#print axioms S3069_factorization_of_range
#print axioms S3069_rangeInclusion_of_data

end LeanFormal.IUT.XiFPaper.S3069RangeInclusionActual
end
