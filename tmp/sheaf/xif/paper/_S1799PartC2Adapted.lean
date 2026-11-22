import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual

noncomputable section
set_option maxHeartbeats 4000000
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual

universe u
variable (R : Type u) [CommRing R]

theorem unitApp_hom_unop_apply' (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ∀ y : ↑(Opposite.unop ((algToCover R ⋙ coverToAlg R).obj A)).obj,
      (CommAlgCat.Hom.hom (unitApp R A).hom.unop.hom) y =
        (Scheme.ΓSpecIso (CommRingCat.of (A.unop).obj)).hom.hom y := fun y => rfl

theorem unitApp_naturality {A B : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A ⟶ B) :
    f ≫ (unitApp R B).hom = (unitApp R A).hom ≫ (algToCover R ⋙ coverToAlg R).map f := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CategoryTheory.unop_comp, ObjectProperty.FullSubcategory.comp_hom,
    CommAlgCat.hom_comp, AlgHom.comp_apply, Functor.comp_map,
    unitApp_hom_unop_apply' R B, unitApp_hom_unop_apply' R A]
  have hnat := congrArg
    (fun (g : Γ(Spec (CommRingCat.of (B.unop.obj)), ⊤) ⟶ CommRingCat.of (A.unop.obj)) => g.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f.unop.hom.hom.toRingHom)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  exact hnat.symm

/-- The unit of the comparison. -/
noncomputable def unitIso :
    𝟭 (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ≅ algToCover R ⋙ coverToAlg R :=
  NatIso.ofComponents (fun A => unitApp R A) (fun {A B} f => unitApp_naturality R f)

theorem unitIso_hom_app (X : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (unitIso R).hom.app X = (unitApp R X).hom := rfl

theorem counitIso_hom_app (C : FiniteEtaleCover (specBase R)) :
    (counitIso R).hom.app C = (counitApp R C).hom := rfl

/-- The triangle identity for the two-sided comparison. -/
theorem functor_unitIso_comp (X : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (algToCover R).map ((unitIso R).hom.app X) ≫
        (counitIso R).hom.app ((algToCover R).obj X) = 𝟙 ((algToCover R).obj X) := by
  rw [unitIso_hom_app R X, counitIso_hom_app R ((algToCover R).obj X)]
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    overComp_left, overId_left, Functor.id_obj]
  have h1 := algToCover_map_left R ((unitApp R X).hom)
  have h2 := counitApp_hom_left R ((algToCover R).obj X)
  rw [h1, h2]
  have h3 : (CommAlgCat.Hom.hom (unitApp R X).hom.unop.hom).toRingHom =
      ((Scheme.ΓSpecIso (CommRingCat.of (X.unop).obj)).hom :
        ↑(((algToCover R ⋙ coverToAlg R).obj X).unop).obj →+* ↑(X.unop).obj) := rfl
  rw [h3]
  have h4 : ((algToCover R).obj X).carrier.isoSpec.inv =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of (X.unop).obj)).inv :=
    Scheme.isoSpec_Spec_inv _
  rw [h4, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

/-- **The two-sided affine finite-etale comparison**. -/
noncomputable def affineFiniteEtaleEquivalenceTwoSided :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ≌ FiniteEtaleCover (specBase R) where
  functor := algToCover R
  inverse := coverToAlg R
  unitIso := unitIso R
  counitIso := counitIso R
  functor_unitIso_comp := functor_unitIso_comp R

end LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual