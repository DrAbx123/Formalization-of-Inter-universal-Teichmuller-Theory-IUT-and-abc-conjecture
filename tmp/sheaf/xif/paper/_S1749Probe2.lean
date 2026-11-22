/-
S1749 probe (not part of the deliverable): record, by instance search at this
Mathlib commit, that none of the five open fields is available in Mathlib.
Every example in this file is *expected* to fail; the failures are the evidence.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

universe u

open CategoryTheory CategoryTheory.Limits

variable (K : Type u) [Field K]

namespace S1749ProbeMissing

/-- Field 2 via the closure statement that would produce it. -/
example : (CommAlgCat.finiteEtale.{u} K).IsClosedUnderColimitsOfShape WalkingCospan :=
  inferInstance

/-- Field 2 directly. -/
example : HasPullbacks ((CommAlgCat.FiniteEtale.{u} K)^op) := inferInstance

/-- Field 3 via the closure statement. -/
example : (CommAlgCat.finiteEtale.{u} K).IsClosedUnderLimitsOfShape (Discrete PUnit) :=
  inferInstance

/-- Field 3 directly (finite products in FiniteEtale K). -/
example : HasFiniteProducts (CommAlgCat.FiniteEtale.{u} K) := inferInstance

/-- Field 4 via the closure statement. -/
example {G : Type u} [Group G] [Finite G] :
    (CommAlgCat.finiteEtale.{u} K).IsClosedUnderLimitsOfShape (SingleObj G) :=
  inferInstance

/-- Field 4 directly. -/
example : HasFiniteCoproducts ((CommAlgCat.FiniteEtale.{u} K)^op) := inferInstance

/-- Field 5's useful consequence: coproduct inclusions are monic. -/
example : MonoCoprod ((CommAlgCat.FiniteEtale.{u} K)^op) := inferInstance

/-- Field 6: the fibre functor at the algebraic closure. -/
example : PreGaloisCategory.FiberFunctor
    (CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)) := inferInstance

end S1749ProbeMissing
