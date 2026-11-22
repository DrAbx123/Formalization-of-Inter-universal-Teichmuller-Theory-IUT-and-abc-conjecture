import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace ProbeS1770
universe u

variable {K : Type u} [Field K]

-- sanity: object API
example (A : CommAlgCat.FiniteEtale.{u} K) : Module.Finite K A := inferInstance
example (A : CommAlgCat.FiniteEtale.{u} K) : Algebra.Etale K A := inferInstance
example (A : CommAlgCat.FiniteEtale.{u} K) : CommRing A := inferInstance

variable (G : Type u) [Group G] [Finite G]

example : (SingleObj G)ᵒᵖ = Opposite (SingleObj G) := rfl
example : Category ((SingleObj G)ᵒᵖ) := inferInstance
example (star : SingleObj G) : (Opposite.op star) = (op star) := rfl

-- test: is the hom type G definitionally?
example (j : (SingleObj G)ᵒᵖ) : (j ⟶ j) = G := rfl

end ProbeS1770
