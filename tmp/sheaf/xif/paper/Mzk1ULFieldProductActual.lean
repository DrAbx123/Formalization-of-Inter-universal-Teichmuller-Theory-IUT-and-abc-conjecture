/- U-L explicit field product with explicit e: the actual tensor block decomposes
into actual field factors E j and an actual Q_p-algebra equivalence e. -/
import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import tmp.sheaf.xif.paper.Mzk1P6StepVESupportFinalAct
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULFieldProductActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- Explicit finite-étale field product of the actual tensor block: the actual
field factors `E j`, their local-field structures, and the actual
`ℚ_p`-algebra equivalence `e` to the product. -/
structure ULFieldProductData (tuple : (i : ι) → V i) where
  J : Type (max u v)
  [fintype : Fintype J]
  E : J → Type (max u v)
  [field : ∀ j, NontriviallyNormedField (E j)]
  [alg : ∀ j, NormedAlgebra ℚ_[p] (E j)]
  /-- The actual algebra equivalence between the tensor block and the field product. -/
  equiv : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)
  finite : ∀ j, FiniteDimensional ℚ_[p] (E j)
/-- The explicit actual field-product decomposition, taken from the actual
tensor-core witness. -/
noncomputable def ulFieldProduct (tuple : (i : ι) → V i) :
    ULFieldProductData places tuple :=
  let W := tensorCoreWitness places tuple
  letI : Fintype W.J := W.fintype
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[p] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[p] (W.E j) := W.finite
  { J := W.J
    fintype := W.fintype
    E := W.E
    field := W.field
    alg := W.alg
    equiv := W.equiv
    finite := W.finite }
/-- The explicit actual field-product decomposition exists. -/
theorem ulFieldProduct_exists (tuple : (i : ι) → V i) :
    Nonempty (ULFieldProductData places tuple) :=
  ⟨ulFieldProduct places tuple⟩
#print axioms ulFieldProduct
#print axioms ulFieldProduct_exists
end LeanFormal.IUT.XiFPaper.Mzk1ULFieldProductActual
end
