import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

variable {K : Type} [Field K]

#check @CommAlgCat.FiniteEtale.baseChange
#check @CommAlgCat.FiniteEtale.baseChange_map
#check @Algebra.TensorProduct.map
#check @CommAlgCat.algEquivOfIso
#check @Module.FaithfullyFlat.lTensor_bijective_iff_bijective
#check @AlgEquiv.ofBijective
#check @CommAlgCat.FiniteEtale.isoMk
#check @CategoryTheory.ConcreteCategory.isIso_iff_bijective
#check @CategoryTheory.isIso_iff_of_reflects_iso
#check @Functor.ReflectsIsomorphisms.reflects

example (A B : CommAlgCat.FiniteEtale.{0} K) (f : A ⟶ B) :
    ((CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)).map f).hom.hom =
      Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure K) (AlgebraicClosure K)) f.hom.hom := rfl

end S1769Probe