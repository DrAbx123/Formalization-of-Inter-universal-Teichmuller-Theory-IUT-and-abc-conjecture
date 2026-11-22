import tmp.sheaf.n8.closure.C7QPilotUnitRefTransport
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition

/-!
# One-factor canonical algebra equivalence

The linear equivalence is `PiTensorProduct.subsingletonEquiv`.  The tensor
block has actual `CommRing`/`Algebra ℚ_[p]` instances from
`FinitePadicTensorFieldDecomposition`, but Mathlib supplies no algebra
equivalence for a one-factor `PiTensorProduct`; upgrading the linear
equivalence needs `map_one`/`map_mul`, which are not available as
`PiTensorProduct` singleton algebra lemmas.  This is the exact Mathlib gap.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7OneFactorAlgEquiv

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

abbrev PaperBlock : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

/-- Actual `CommRing` instance on the one-factor tensor block. -/
example : CommRing (PaperBlock S) := inferInstance

/-- Actual `Algebra ℚ_[p]` instance on the one-factor tensor block. -/
example : Algebra ℚ_[pNat S] (PaperBlock S) := inferInstance

/-- The actual linear one-factor equivalence. -/
noncomputable def linearOneFactor : PaperBlock S ≃ₗ[ℚ_[pNat S]] PaperKf S :=
  PiTensorProduct.subsingletonEquiv (R := ℚ_[pNat S])
    (s := fun _ : Unit => PaperKf S) ()

/-- Exact missing Mathlib algebra upgrade: no one-factor `PiTensorProduct`
algebra equivalence is provided, and `subsingletonEquiv` has no
`map_one`/`map_mul` lemmas. -/
def MissingOneFactorTensorAlgEquiv : Prop :=
  Nonempty (PaperBlock S ≃ₐ[ℚ_[pNat S]] PaperKf S)

end LeanFormal.IUT.N8Closure.C7OneFactorAlgEquiv

end