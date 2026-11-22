import Mathlib.RingTheory.Etale.Finite
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.HasLimits

open CategoryTheory CategoryTheory.Limits

universe u

namespace S1771

variable {K : Type u} [Field K]

/-- The binary fan with point B and legs f : B → A, g : B → C is a limit when
B ≃ A × C and f, g are the two projections. -/
noncomputable def binaryFan_isLimit_of_algEquiv_prod
    {A B C : Type u} [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    [CommRing C] [Algebra K C] [Module.Finite K C] [Algebra.Etale K C]
    (e : B ≃ₐ[K] (A × C)) :
    IsLimit (BinaryFan.mk
      (CommAlgCat.FiniteEtale.ofHom ((AlgHom.fst K A C).comp e.toAlgHom))
      (CommAlgCat.FiniteEtale.ofHom ((AlgHom.snd K A C).comp e.toAlgHom))) := by
  let f : B →ₐ[K] A := (AlgHom.fst K A C).comp e.toAlgHom
  let g : B →ₐ[K] C := (AlgHom.snd K A C).comp e.toAlgHom
  change IsLimit (BinaryFan.mk (CommAlgCat.FiniteEtale.ofHom f)
    (CommAlgCat.FiniteEtale.ofHom g))
  refine BinaryFan.IsLimit.mk _ (fun {T} p q => ?_) ?_ ?_ ?_
  · let h : (T : Type u) →ₐ[K] B :=
      e.symm.toAlgHom.comp (AlgHom.prod p.hom.hom q.hom.hom)
    exact ObjectProperty.homMk (CommAlgCat.ofHom h)
  · intro T p q
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    simp only [ObjectProperty.FullSubcategory.comp_hom, AlgHom.comp_apply, AlgHom.fst_apply,
      AlgHom.prod_apply]
    rfl
  · intro T p q
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    simp only [ObjectProperty.FullSubcategory.comp_hom, AlgHom.comp_apply, AlgHom.snd_apply,
      AlgHom.prod_apply]
    rfl
  · intro T p q m hm1 hm2
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    -- show m x = e.symm (p x, q x)
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    have hm1' : f (m.hom.hom x) = p.hom.hom x := by
      have h := congrArg (fun (k : T ⟶ CommAlgCat.FiniteEtale.of K A) => k.hom.hom x) hm1
      simpa [BinaryFan.mk, f] using h
    have hm2' : g (m.hom.hom x) = q.hom.hom x := by
      have h := congrArg (fun (k : T ⟶ CommAlgCat.FiniteEtale.of K C) => k.hom.hom x) hm2
      simpa [BinaryFan.mk, g] using h
    -- e (m x) = (f (m x), g (m x))
    change e (m.hom.hom x) = (p.hom.hom x, q.hom.hom x)
    rw [← hm1', ← hm2']
    rfl

end S1771
