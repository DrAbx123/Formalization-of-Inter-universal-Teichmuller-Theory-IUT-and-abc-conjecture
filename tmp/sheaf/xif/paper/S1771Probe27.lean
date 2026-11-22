import Mathlib.RingTheory.Etale.Finite
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K]
variable {A B C : Type u} [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    [CommRing C] [Algebra K C] [Module.Finite K C] [Algebra.Etale K C]
    (e : B ≃ₐ[K] (A × C))
example (T : CommAlgCat.FiniteEtale K) (p : T ⟶ CommAlgCat.FiniteEtale.of K A)
    (q : T ⟶ CommAlgCat.FiniteEtale.of K C) :
    (ObjectProperty.homMk (P := CommAlgCat.finiteEtale K)
      (CommAlgCat.ofHom (e.symm.toAlgHom.comp (AlgHom.prod p.hom.hom q.hom.hom))) : T ⟶ CommAlgCat.FiniteEtale.of K B) = 
    ObjectProperty.homMk (P := CommAlgCat.finiteEtale K)
      (CommAlgCat.ofHom (e.symm.toAlgHom.comp (AlgHom.prod p.hom.hom q.hom.hom))) := rfl
#check ObjectProperty.homMk_hom
#check ObjectProperty.FullSubcategory.homMk
