import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

variable {K : Type} [Field K]

example : (forget (CommAlgCat.FiniteEtale.{0} K)).ReflectsIsomorphisms := by infer_instance

example (A B : CommAlgCat.FiniteEtale.{0} K) (f : A ⟶ B) :
    ((CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)).map f).hom.hom =
      Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure K) (AlgebraicClosure K)) f.hom.hom := rfl

#check @CommAlgCat.FiniteEtale.baseChange_obj
#check @CommAlgCat.FiniteEtale.baseChange_map

end S1769Probe