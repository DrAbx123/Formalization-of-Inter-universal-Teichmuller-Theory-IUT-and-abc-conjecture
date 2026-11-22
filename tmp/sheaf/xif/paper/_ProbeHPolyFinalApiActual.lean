/- API probe for the hPoly final assembly (throwaway). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyEvalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyCoverActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.ProbeHPolyFinalApi
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual

variable (h : Polynomial ℚ)

/-- candidate intersection ring: localization of D(hRev) at the image of lambda -/
abbrev Tint (h : Polynomial ℚ) : Type :=
  Localization.Away (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) (Polynomial.X))

example : CommRing (Tint h) := inferInstance
example : Algebra (Polynomial ℚ) (Tint h) := inferInstance
example : Algebra (Localization.Away (hRev h)) (Tint h) := inferInstance
example : IsScalarTower (Polynomial ℚ) (Localization.Away (hRev h)) (Tint h) := inferInstance
example : IsScalarTower ℚ (Localization.Away (hRev h)) (Tint h) := inferInstance
example : IsScalarTower ℚ (Polynomial ℚ) (Tint h) := inferInstance
example : IsLocalization.Away (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) (Tint h) := inferInstance
example : IsLocalization.Away (hRev h * Polynomial.X) (Tint h) := inferInstance
example : IsUnit (algebraMap (Polynomial ℚ) (Tint h) (Polynomial.X)) :=
  IsLocalization.Away.isUnit_of_dvd (S := Tint h) (x := hRev h * Polynomial.X)
    (r := Polynomial.X) (dvd_mul_left _ _)
example : IsUnit (algebraMap (Polynomial ℚ) (Tint h) (hRev h)) :=
  IsLocalization.Away.isUnit_of_dvd (S := Tint h) (x := hRev h * Polynomial.X)
    (r := hRev h) (dvd_mul_right _ _)

-- the chart inclusion of the intersection into the D(hRev) piece
example : Spec (CommRingCat.of (Tint h)) ⟶ Spec (CommRingCat.of (Localization.Away (hRev h))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (hRev h)) (Tint h)))
example : IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (Localization.Away (hRev h)) (Tint h)))) := inferInstance
example : (Spec.map (CommRingCat.ofHom
    (algebraMap (Localization.Away (hRev h)) (Tint h)))).opensRange =
    (PrimeSpectrum.basicOpen (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) :
      TopologicalSpace.Opens (PrimeSpectrum (Localization.Away (hRev h)))) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Localization.Away (hRev h)))
    (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X)

-- generic preimage of a basic open along Spec.map
theorem specMap_preimage_basicOpen_test {R S : Type} [CommRing R] [CommRing S] (rho : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom rho)) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (rho r) : TopologicalSpace.Opens (PrimeSpectrum S)) :=
  PrimeSpectrum.comap_basicOpen rho r

example : Mono hPolyPiece1 := inferInstance
example : Mono (hPolyPiece2 h) := inferInstance
example : Mono localChart0 := inferInstance

#check @IsOpenImmersion.isPullback
#check @Scheme.Cover.glueMorphisms
#check @Scheme.Cover.ι_glueMorphisms
#check @Scheme.Hom.comp_preimage
#check @Scheme.Hom.opensRange_comp
#check @Scheme.Hom.preimage_image_eq
#check @Scheme.Hom.opensRange_localizationAway
#check @IsLocalization.Away.lift_comp
#check @PrimeSpectrum.comap_basicOpen
#check @pullbackSymmetry_hom_comp_fst
#check @pullbackSymmetry_hom_comp_snd
#check @IsLocalization.Away.isUnit_of_dvd
#check @IsLocalization.Away.invSelf
#check @IsLocalization.Away.mul_invSelf
#check @IsUnit.unit_spec
#check @Units.val_pow_eq_pow_val
#check @IsScalarTower.algebraMap_apply
#check @IsPullback.isoPullback_hom_fst
#check @IsPullback.isoPullback_hom_snd
#check @IsLocalization.Away.lift_eq
#check @IsLocalization.Away.lift
#check @evalAt_C
#check @evalAt_X
#check @chartMorphism_transition
#check @Polynomial.C_eq_algebraMap
#check @IsLocalization.Away.algebraMap_isUnit

end LeanFormal.IUT.XiFPaper.ProbeHPolyFinalApi
