import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

variable {K : Type} [Field K]

abbrev bc (K : Type) [Field K] : CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

example (A B : CommAlgCat.FiniteEtale.{0} K) (f : A ⟶ B) :
    (↥(((bc K).obj A).obj) : Type) = ((AlgebraicClosure K) ⊗[K] (A.obj : Type)) := rfl

example (A B : CommAlgCat.FiniteEtale.{0} K) (f : A ⟶ B)
    (hbij : Function.Bijective (((bc K).map f).hom.hom)) :
    Function.Bijective (fun x : (AlgebraicClosure K) ⊗[K] (A.obj : Type) =>
      LinearMap.lTensor (AlgebraicClosure K) f.hom.hom.toLinearMap x) := by
  change Function.Bijective (fun x : (AlgebraicClosure K) ⊗[K] (A.obj : Type) =>
      (((bc K).map f).hom.hom) x) at hbij
  simpa only [CommAlgCat.FiniteEtale.baseChange] using hbij

end S1769Probe