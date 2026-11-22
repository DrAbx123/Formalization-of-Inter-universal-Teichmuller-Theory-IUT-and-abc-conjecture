import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Category.CommAlgCat.Basic

open CategoryTheory CategoryTheory.Limits

universe u

namespace S1771

variable {K : Type u} [Field K]

#check Algebra.FinitePresentation.of_finiteType
#check Algebra.FinitePresentation.iff_finiteType
#check Algebra.FinitePresentation.of_finiteType

example (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B] (J : Ideal B) :
    Algebra.FinitePresentation K (B ⧸ J) := by
  exact (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance

end S1771
