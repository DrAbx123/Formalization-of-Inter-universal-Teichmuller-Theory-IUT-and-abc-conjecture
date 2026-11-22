import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# A genuine finite p-adic tensor with its finite-dimensional topology

The carrier is the universal algebraic Qp tensor, with a norm pulled
back from the coordinates of the tensor product of finite bases.
Pure tensors have polynomial coordinates, which proves continuity.
No normed tensor structure is assumed as an interface obligation.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

open scoped TensorProduct

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]

def FinitePadicTensor := ⨂[ℚ_[p]] i, M i

instance finitePadicTensorAddCommGroup : AddCommGroup (FinitePadicTensor (p := p) M) :=
  inferInstanceAs (AddCommGroup (⨂[ℚ_[p]] i, M i))

instance finitePadicTensorModule : Module ℚ_[p] (FinitePadicTensor (p := p) M) :=
  inferInstanceAs (Module ℚ_[p] (⨂[ℚ_[p]] i, M i))

omit [Fintype ι] in
instance finitePadicTensorFinite [Finite ι] :
    FiniteDimensional ℚ_[p] (FinitePadicTensor (p := p) M) :=
  inferInstanceAs (FiniteDimensional ℚ_[p] (⨂[ℚ_[p]] i, M i))

abbrev FinitePadicTensorIndex := (i : ι) → Fin (Module.finrank ℚ_[p] (M i))

instance finitePadicTensorIndexFintype : Fintype (FinitePadicTensorIndex (p := p) M) := by
  classical
  infer_instance

def finitePadicTensorCoordinates :
    FinitePadicTensor (p := p) M ≃ₗ[ℚ_[p]] (FinitePadicTensorIndex (p := p) M → ℚ_[p]) :=
  (Basis.piTensorProduct (fun i => Module.finBasis ℚ_[p] (M i))).equivFun

instance finitePadicTensorNormedAddCommGroup :
    NormedAddCommGroup (FinitePadicTensor (p := p) M) :=
  NormedAddCommGroup.induced _ _ (finitePadicTensorCoordinates (p := p) M).toAddMonoidHom
    (finitePadicTensorCoordinates (p := p) M).injective

instance finitePadicTensorNormedSpace : NormedSpace ℚ_[p] (FinitePadicTensor (p := p) M) :=
  NormedSpace.induced ℚ_[p] _ _ (finitePadicTensorCoordinates (p := p) M)

instance finitePadicTensorProperSpace : ProperSpace (FinitePadicTensor (p := p) M) :=
  FiniteDimensional.proper ℚ_[p] (FinitePadicTensor (p := p) M)

def finitePadicTensorTprod : MultilinearMap ℚ_[p] M (FinitePadicTensor (p := p) M) :=
  PiTensorProduct.tprod ℚ_[p]

theorem finitePadicTensorCoordinates_tprod (x : (i : ι) → M i)
    (j : FinitePadicTensorIndex (p := p) M) :
    finitePadicTensorCoordinates (p := p) M (finitePadicTensorTprod (p := p) M x) j =
      ∏ i, (Module.finBasis ℚ_[p] (M i)).repr (x i) (j i) := by
  exact Basis.piTensorProduct_repr_tprod_apply
    (fun i => Module.finBasis ℚ_[p] (M i)) x j

theorem continuous_finitePadicTensorTprod : Continuous (finitePadicTensorTprod (p := p) M) := by
  have hcoordinates : Continuous (fun x : (i : ι) → M i =>
      finitePadicTensorCoordinates (p := p) M (finitePadicTensorTprod (p := p) M x)) := by
    apply continuous_pi
    intro j
    simp_rw [finitePadicTensorCoordinates_tprod]
    apply continuous_finsetProd
    intro i _
    exact ((Module.finBasis ℚ_[p] (M i)).coord (j i)).continuous_of_finiteDimensional.comp
      (continuous_apply i)
  have hinverse := (finitePadicTensorCoordinates (p := p) M).symm.toContinuousLinearEquiv.continuous
  have hcomposite := hinverse.comp hcoordinates
  change Continuous (fun x => (finitePadicTensorCoordinates (p := p) M).symm
    (finitePadicTensorCoordinates (p := p) M (finitePadicTensorTprod (p := p) M x))) at hcomposite
  simpa only [LinearEquiv.symm_apply_apply] using hcomposite

def finitePadicTensorContinuousTprod :
    ContinuousMultilinearMap ℚ_[p] M (FinitePadicTensor (p := p) M) :=
  ⟨finitePadicTensorTprod (p := p) M, continuous_finitePadicTensorTprod (p := p) M⟩

end

end LeanFormal.IUT.LocalFieldPadicTensor
