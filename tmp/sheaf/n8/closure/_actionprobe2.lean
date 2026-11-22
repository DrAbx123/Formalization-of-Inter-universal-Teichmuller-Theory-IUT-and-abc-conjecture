import tmp.sheaf.n8.closure.EtaTensorDetProductActual
import tmp.sheaf.n8.closure.EtaTensorBlockDetActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open scoped TensorProduct
namespace Probe2
universe u
variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)
abbrev RestIdx := {i : ι // i ≠ j}
abbrev Rest := (⨂[ℚ_[p]] (i : RestIdx j), A i)
def splitEquiv : ι ≃ Unit ⊕ RestIdx j where
  toFun i := if h : i = j then Sum.inl () else Sum.inr ⟨i, h⟩
  invFun s := Sum.rec (fun _ => j) (fun x => x.1) s
  left_inv i := by by_cases h : i = j <;> simp [h]
  right_inv s := by cases s with | inl _ => simp | inr x => simp [x.2]
abbrev SumFamily (j : ι) : Unit ⊕ RestIdx j → Type := Sum.rec (fun _ => A j) (fun i => A i)
instance (j : ι) (i : Unit ⊕ RestIdx j) : AddCommMonoid (SumFamily A j i) := by rcases i with (_ | x) <;> infer_instance
instance (j : ι) (i : Unit ⊕ RestIdx j) : Module ℚ_[p] (SumFamily A j i) := by rcases i with (_ | x) <;> infer_instance
def splitFamilyEquiv (i : Unit ⊕ RestIdx j) :
    A ((splitEquiv j).symm i) ≃ₗ[ℚ_[p]] SumFamily A j i := by
  rcases i with (_ | x)
  · exact LinearEquiv.refl ℚ_[p] (A j)
  · exact LinearEquiv.refl ℚ_[p] (A x.1)
def splitTensorEquiv :
    (⨂[ℚ_[p]] (i : ι), A i) ≃ₗ[ℚ_[p]]
      TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) :=
  (PiTensorProduct.reindex ℚ_[p] A (splitEquiv j)).trans
    ((PiTensorProduct.congr (splitFamilyEquiv (p := p) A j)).trans
      ((PiTensorProduct.tmulEquivDep ℚ_[p] (SumFamily A j)).symm.trans
        (TensorProduct.congr
          (PiTensorProduct.subsingletonEquiv (R := ℚ_[p]) (s := fun _ : Unit => A j) ())
          (LinearEquiv.refl ℚ_[p] (Rest (p := p) A j)))))
def binaryAction (g : A j) :
    TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) →ₗ[ℚ_[p]]
      TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) :=
  TensorProduct.map (LinearMap.mulLeft ℚ_[p] g) LinearMap.id
def tensorActionMul (g : A j) :
    (⨂[ℚ_[p]] (i : ι), A i) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] (i : ι), A i) :=
  LinearMap.mulLeft ℚ_[p] (PiTensorProduct.tprod ℚ_[p] (fun i => if h : i = j then h ▸ g else 1))
@[simp] theorem restIdx_coe_ne (i : RestIdx j) : (i : ι) ≠ j := i.2

@[simp] theorem splitEquiv_symm_inl : (splitEquiv j).symm (Sum.inl ()) = j := rfl
@[simp] theorem splitEquiv_symm_inr (x : RestIdx j) :
    (splitEquiv j).symm (Sum.inr x) = x.1 := rfl
@[simp] theorem splitFamilyEquiv_inl :
    splitFamilyEquiv (p := p) A j (Sum.inl ()) =
      LinearEquiv.refl ℚ_[p] (A j) := rfl
@[simp] theorem splitFamilyEquiv_inr (x : RestIdx j) :
    splitFamilyEquiv (p := p) A j (Sum.inr x) =
      LinearEquiv.refl ℚ_[p] (A x.1) := rfl

theorem split_action (g : A j) :
    (splitTensorEquiv (p := p) A j).toLinearMap.comp
        (tensorActionMul (p := p) A j g) =
      (binaryAction (p := p) A j g).comp
        (splitTensorEquiv (p := p) A j).toLinearMap := by
  apply PiTensorProduct.ext
  ext x
  change splitTensorEquiv (p := p) A j
      (tensorActionMul (p := p) A j g (PiTensorProduct.tprod ℚ_[p] x)) =
    binaryAction (p := p) A j g
      (splitTensorEquiv (p := p) A j (PiTensorProduct.tprod ℚ_[p] x))
  rw [show tensorActionMul (p := p) A j g =
      LinearMap.mulLeft ℚ_[p] (PiTensorProduct.tprod ℚ_[p]
        (fun i => if h : i = j then h ▸ g else 1)) from rfl]
  rw [LinearMap.mulLeft_apply, PiTensorProduct.tprod_mul_tprod]
  simp [splitTensorEquiv, binaryAction, PiTensorProduct.reindex_tprod,
    PiTensorProduct.congr_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod,
    LinearEquiv.refl_apply, TensorProduct.congr_tmul, TensorProduct.map_tmul]
  rfl
end Probe2
