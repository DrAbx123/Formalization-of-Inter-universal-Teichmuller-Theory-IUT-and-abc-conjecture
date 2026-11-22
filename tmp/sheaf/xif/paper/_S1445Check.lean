import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization

noncomputable section
open scoped TensorProduct
namespace Check1445
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
universe u v
variable {p : ℕ} [Fact p.Prime] {j : ℕ}
variable {VQ : Type u} {Place : VQ → Type v} (vQ : VQ) [Fintype (Place vQ)]
variable (A : (i : Capsule j) → Place vQ → Type)
variable [∀ i v, NormedField (A i v)]
variable [∀ i v, NormedAlgebra ℚ_[p] (A i v)]
variable [∀ i v, FiniteDimensional ℚ_[p] (A i v)]
variable [∀ i v, CharZero (A i v)]
variable [∀ i v, IsUltrametricDist (A i v)]
variable [∀ i v, CompleteSpace (A i v)]
variable [∀ i v, ProperSpace (A i v)]
abbrev Tup := (i : Capsule j) → Place vQ
abbrev Blk (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :=
  FinitePadicTensor (p := p) (fun i => A i (t i))
noncomputable def ratTo (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :
    (⨂[ℚ] i : Capsule j, A i (t i)) →ₗ[ℚ] Blk (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t :=
  PiTensorProduct.lift ((finitePadicTensorTprod (p := p) (fun i => A i (t i))).restrictScalars ℚ)
#check @ratTo
end Check1445
