import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

noncomputable section

namespace ABCBridge.IsospecSectionsCoherence

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

end ABCBridge.IsospecSectionsCoherence
