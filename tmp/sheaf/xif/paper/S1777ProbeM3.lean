import tmp.sheaf.xif.paper.S1777AffineCoverAlgebrasActual
import Mathlib.RingTheory.Etale.Finite

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1777AffineCoverAlgebrasActual

namespace M1

noncomputable def sliceAlgebra (X : S1733Slice) : S1777Algᵒᵖ :=
  letI : Algebra S1777R (↥X.left.unop) := (S1777AlgMap X).hom.toAlgebra
  letI : Module.Finite S1777R (↥X.left.unop) := by
    rw [← RingHom.finite_algebraMap, RingHom.algebraMap_toAlgebra]
    exact S1777AlgMap_finite X
  letI : Algebra.Etale S1777R (↥X.left.unop) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact S1777AlgMap_etale X
  Opposite.op (CommAlgCat.FiniteEtale.of S1777R (↥X.left.unop))

lemma sliceAlgebra_algebraMap (X : S1733Slice) :
    (algebraMap S1777R ↥(sliceAlgebra X).unop : S1777R →+* ↥X.left.unop) =
      (S1777AlgMap X).hom :=
  RingHom.algebraMap_toAlgebra (S1777AlgMap X).hom

lemma obj_sliceAlgebra_left (X : S1733Slice) :
    (S1777Obj (sliceAlgebra X)).left = X.left := rfl

lemma obj_sliceAlgebra_hom (X : S1733Slice) :
    (S1777Obj (sliceAlgebra X)).hom = X.hom := by
  show Spec.map (CommRingCat.ofHom (algebraMap S1777R (↥(sliceAlgebra X).unop))) = X.hom
  rw [sliceAlgebra_algebraMap X, CommRingCat.ofHom_hom, S1777SpecMapAlgMap]

noncomputable def sliceIso (X : S1733Slice) : S1777Obj (sliceAlgebra X) ≅ X :=
  MorphismProperty.CostructuredArrow.isoMk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := S1777Base) (Iso.refl _) (by trivial) (by trivial) (by
      show Scheme.Spec.map (Iso.refl _).hom ≫ X.hom = (S1777Obj (sliceAlgebra X)).hom
      rw [Iso.refl_hom, Scheme.Spec.map_id, Category.id_comp, obj_sliceAlgebra_hom])

instance sliceFunctor_essSurj : S1777SliceFunctor.EssSurj :=
  ⟨fun X => ⟨sliceAlgebra X, ⟨sliceIso X⟩⟩⟩

end M1
