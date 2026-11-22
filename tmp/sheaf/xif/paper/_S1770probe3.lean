import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace ProbeS1770
universe u

variable {K : Type u} [Field K]
variable (G : Type u) [Group G] [Finite G]

-- Q1: is F.obj j defeq to F.obj star for j : SingleObj G?
example (F : SingleObj G ⥤ CommAlgCat.FiniteEtale.{u} K) (j : SingleObj G)
    (u : F.obj (SingleObj.star G) ⟶ F.obj (SingleObj.star G)) : F.obj j ⟶ F.obj j := u

-- Q2: same for the op shape
example (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) (j : (SingleObj G)ᵒᵖ)
    (u : F.obj (Opposite.op (SingleObj.star G)) ⟶ F.obj (Opposite.op (SingleObj.star G))) :
    F.obj j ⟶ F.obj j := u

-- Q3: natTrans style for op shape
example (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    (u : F.obj (Opposite.op (SingleObj.star G)) ⟶ F.obj (Opposite.op (SingleObj.star G)))
    (h : ∀ f : (F.obj (Opposite.op (SingleObj.star G)) ⟶ F.obj (Opposite.op (SingleObj.star G))),
      True) :
    (Functor.const (SingleObj G)ᵒᵖ).obj (F.obj (Opposite.op (SingleObj.star G))) ⟶ F :=
  { app := fun j => u
    naturality := by intro j j' f; sorry }

end ProbeS1770
