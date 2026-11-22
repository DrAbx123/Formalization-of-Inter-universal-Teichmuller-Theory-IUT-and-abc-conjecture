import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe31

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

lemma finite_of_iso_commRingCat {A B : CommRingCat} (f : A ⟶ B) [IsIso f] :
    RingHom.Finite f.hom :=
  RingHom.Finite.of_surjective f.hom
    ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance).2

lemma etale_of_iso_commRingCat {A B : CommRingCat} (f : A ⟶ B) [IsIso f] :
    RingHom.Etale f.hom :=
  RingHom.Etale.of_bijective ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance)

/-- The algebra map R' -> global sections of the affine model. -/
noncomputable def algMap (X : S1733Slice) : CommRingCat.of R ⟶ X.left.unop :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom

theorem Spec_map_algMap (X : S1733Slice) : Spec.map (algMap X) = X.hom := by
  have h := Scheme.isoSpec_hom_naturality X.hom
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_hom] at h
  rw [← Spec.map_comp] at h
  rw [algMap, Category.assoc, Spec.map_comp, Spec.map_comp, Spec.map_inv]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma appTop_finite (X : S1733Slice) : RingHom.Finite (X.hom.appTop).hom := by
  have h : IsFinite X.hom := X.prop.1
  have key := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := X.hom)).mp h
  exact key.2

lemma appTop_etale (X : S1733Slice) : RingHom.Etale (X.hom.appTop).hom := by
  have h : Etale X.hom := X.prop.2
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale) (Q := @RingHom.Etale)
    (f := X.hom)).mp h

end Probe31
