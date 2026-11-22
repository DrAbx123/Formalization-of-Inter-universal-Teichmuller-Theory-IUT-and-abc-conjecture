/-
S1794 import check: a downstream file can import the module and use its statements.
-/
import tmp.sheaf.xif.paper.S1794FiberFunctorProductActual

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1794Check

variable (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]

-- Field 1 of the six, at the shape demanded by PreGaloisCategory.FiberFunctor
example : PreservesLimitsOfShape (Discrete PEmpty.{1}) (S1794.F K Ω) :=
  S1794.preservesTerminalObjects_pempty K Ω

-- the product decomposition, ready for consumers
example (A : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    ∃ (I : Type) (_ : Fintype I) (Ai : I → Type) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (e : A ≃ₐ[K] ∀ i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  S1794.exists_prod_fields K A

-- the six field statements are available by name
#check @S1794.PreservesPullbacksField
#check @S1794.fiberFunctorOfFields

end S1794Check
