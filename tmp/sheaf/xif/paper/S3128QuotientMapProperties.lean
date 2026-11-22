import tmp.sheaf.xif.paper.S3128GeneralGlueActual
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3128QuotientMapProperties
open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128GeneralGlueActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {G : Type} [Group G] [Fintype G] {A : Type} [CommRing A] [MulSemiringAction G A]
abbrev S := S3128FixedSubring G A
/-- The fixed subring is an invariant extension. -/
noncomputable instance S3128_isInvariant :
    Algebra.IsInvariant (S3128FixedSubring G A) A G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- A is integral over A^G for finite G (Mathlib invariant charpoly). -/
theorem S3128_fixedSubring_isIntegral [Finite G] :
    Algebra.IsIntegral (S3128FixedSubring G A) A :=
  Algebra.IsInvariant.isIntegral (S3128FixedSubring G A) A G

/-- q is surjective (unconditional for finite G). -/
theorem S3128_specQuotientMap_surjective
    :
    AlgebraicGeometry.Surjective (S3128SpecQuotientMap (G := G) (A := A)) := by
  refine ⟨?_⟩
  intro x
  haveI : Algebra.IsIntegral (S3128FixedSubring G A) A := S3128_fixedSubring_isIntegral
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (S3128FixedSubring G A) A x
  refine ⟨y, ?_⟩
  rw [S3128SpecQuotientMap, Spec.map_apply]
  exact hy
/-- q is flat if A is flat as an A^G-module. -/
theorem S3128_specQuotientMap_flat
    [Module.Flat (S3128FixedSubring G A) A] :
    AlgebraicGeometry.Flat (S3128SpecQuotientMap (G := G) (A := A)) := by
  rw [S3128SpecQuotientMap, AlgebraicGeometry.Flat.SpecMap_iff]
  change RingHom.Flat (algebraMap (S3128FixedSubring G A) A)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance
/-- q is quasi-compact (affine map). -/
theorem S3128_specQuotientMap_quasiCompact :
    AlgebraicGeometry.QuasiCompact (S3128SpecQuotientMap (G := G) (A := A)) := by
  infer_instance
/-- Full conditional fpqc descent: if A is integral and flat over A^G and the
descent compatibility holds, invariant maps descend uniquely. -/
theorem S3128GeneralCoequalizerTarget_of_fpqc_conditions
    (T : Scheme) (u : Spec (CommRingCat.of A) ⟶ T)
    [Module.Flat (S3128FixedSubring G A) A]
    (hcompat : S3128DescentCompat (G := G) (A := A) T u) :
    ∃! (v : Spec (CommRingCat.of (S3128FixedSubring G A)) ⟶ T),
      S3128SpecQuotientMap (G := G) (A := A) ≫ v = u := by
  haveI : AlgebraicGeometry.Surjective (S3128SpecQuotientMap (G := G) (A := A)) :=
    S3128_specQuotientMap_surjective
  haveI : AlgebraicGeometry.Flat (S3128SpecQuotientMap (G := G) (A := A)) :=
    S3128_specQuotientMap_flat
  haveI : AlgebraicGeometry.QuasiCompact (S3128SpecQuotientMap (G := G) (A := A)) :=
    S3128_specQuotientMap_quasiCompact
  exact S3128GeneralCoequalizerTarget_of_fpqc T u hcompat

#check S3128_fixedSubring_isIntegral
#check S3128_specQuotientMap_surjective
#check S3128GeneralCoequalizerTarget_of_fpqc_conditions
#check S3128_specQuotientMap_surjective
#check S3128_specQuotientMap_flat
#check S3128_specQuotientMap_quasiCompact
end LeanFormal.IUT.XiFPaper.S3128QuotientMapProperties
end
