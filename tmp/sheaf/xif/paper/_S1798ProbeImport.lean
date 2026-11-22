import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.FintypeCat

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace ProbeImport

variable (K : Type) [Field K]

#check Algebra.Etale.iff_exists_algEquiv_prod
#check CommAlgCat.FiniteEtale.fiber
#check PreGaloisCategory.FiberFunctor

example : (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ = (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ := rfl

end ProbeImport
