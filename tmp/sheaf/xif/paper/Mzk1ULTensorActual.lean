/- U-L tensor actual: actual field-product decomposition. -/
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTensorActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
noncomputable def uL_tensorDecomp : TensorCoreWitness places tuple :=
  tensorCoreWitness places tuple
theorem uL_tensorDecomp_nonempty : Nonempty (TensorCoreWitness places tuple) :=
  ⟨uL_tensorDecomp places tuple⟩
#print axioms uL_tensorDecomp
#print axioms uL_tensorDecomp_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1ULTensorActual
end
