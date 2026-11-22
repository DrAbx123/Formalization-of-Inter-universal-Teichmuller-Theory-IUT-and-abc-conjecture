import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationSectionsInvariance
import LeanFormal.IUT.Foundations.AlgebraicGeometry.IsospecSectionsCoherence
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open AffineLocalQuotientGluingConstruct

noncomputable section

namespace RegularPermutationActionColimit

universe u

lemma isoSpec_sectionsAlgebraMap {R : Type u} [CommRing R]
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    Z.carrier.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R Γ(Z.carrier, ⊤))) =
      Z.structureMap := by
  letI := finiteEtaleCoverSectionsAlgebra R Z
  change Z.carrier.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (finiteEtaleCoverSectionsAlgebraMap R Z)) =
    Z.structureMap
  unfold finiteEtaleCoverSectionsAlgebraMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  change Z.carrier.isoSpec.hom ≫ Spec.map (Scheme.Hom.appTop Z.structureMap) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = Z.structureMap
  rw [← Category.assoc]
  rw [Scheme.isoSpec_hom_naturality (FiniteEtaleCover.structureMap Z)]
  rw [Scheme.isoSpec_Spec_hom]
  rw [Category.assoc]
  rw [show Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = 𝟙 _ by
      rw [← Spec.map_comp]
      rw [show (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Scheme.ΓSpecIso (CommRingCat.of R)).hom = 𝟙 _ from
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id]
      simp]
  rw [Category.comp_id]



noncomputable def sectionsAlgMapAlgHom {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]
    (c : Cocone (AffineLocalQuotientGluingConstruct.regularPermutationActionFunctor R G)) :
    Γ(c.pt.carrier, ⊤) →ₐ[R] (G → R) := by
  letI := finiteEtaleCoverSectionsAlgebra R c.pt
  refine
    { toRingHom := ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap R G c
      commutes' := fun r => ?_ }
  let Z := c.pt
  let fOver : (regularPermutationCover R G).toOver ⟶ Z.toOver :=
    (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map
      (c.ι.app (SingleObj.star G))
  have hspec : Spec.map (CommRingCat.ofHom
      ((ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap R G c).comp
        (algebraMap R Γ(Z.carrier, ⊤)))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (G → R))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have hφspec : Spec.map (CommRingCat.ofHom
        (ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap R G c)) =
        fOver.left ≫ Z.carrier.isoSpec.hom := by
      convert ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap_spec R G c using 2
      rfl
    erw [hφspec]
    erw [Category.assoc]
    erw [ABCBridge.IsospecSectionsCoherence.isoSpec_sectionsAlgebraMap (R := R) (Z := Z)]
    exact fOver.w
  have hcat : CommRingCat.ofHom
      ((ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap R G c).comp
        (algebraMap R Γ(c.pt.carrier, ⊤))) =
      CommRingCat.ofHom (algebraMap R (G → R)) := by
    apply Spec.map_injective
    exact hspec
  have hring :
      (ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap R G c).comp
        (algebraMap R Γ(c.pt.carrier, ⊤)) = algebraMap R (G → R) :=
    CommRingCat.hom_ext_iff.mp hcat
  exact congrFun (congrArg DFunLike.coe hring) r

lemma sectionsAlgMapAlgHom_invariant {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]
    (c : Cocone (AffineLocalQuotientGluingConstruct.regularPermutationActionFunctor R G))
    (h : G) (b : Γ(c.pt.carrier, ⊤)) :
    groupActionRingEquiv (G → R) G h
      (sectionsAlgMapAlgHom (R := R) c b) =
        sectionsAlgMapAlgHom (R := R) c b :=
  by
    simpa [sectionsAlgMapAlgHom] using
      (ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap_invariant R G c h b)


end RegularPermutationActionColimit
