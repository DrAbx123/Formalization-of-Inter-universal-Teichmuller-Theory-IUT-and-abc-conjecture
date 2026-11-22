import tmp.sheaf.n8.closure.EtaTensorDetProductActual
import tmp.sheaf.n8.closure.EtaTensorBlockDetActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import LeanFormal.IUT.Foundations.LinearAlgebra.FiniteDeterminant

/-!
# Eta tensor split: actual equivalence and pure-tensor action

For E = tensor_i A_i and a chosen factor j, we explicitly construct

  FinitePadicTensor A  ≃  A_j (x) tensor_{i != j} A_i

and prove that the pure-tensor action (multiplication by
1 (x) ... (x) g (x) ... (x) 1) is transported to mult(g) (x) id.

The equivalence is built from Mathlib PiTensorProduct.reindex,
PiTensorProduct.congr, PiTensorProduct.tmulEquivDep, and the singleton tensor
equivalence.  No arbitrary equivalence or action is used.
-/

set_option linter.deprecated false
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open scoped TensorProduct BigOperators

namespace LeanFormal.IUT.N8Closure.EtaTensorSplitActual

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
  left_inv i := by
    by_cases h : i = j <;> simp [h]
  right_inv s := by
    cases s with
    | inl _ => simp
    | inr x => simp [x.2]

abbrev SumFamily (j : ι) : Unit ⊕ RestIdx j → Type :=
  Sum.rec (fun _ => A j) (fun i => A i)

instance (j : ι) (i : Unit ⊕ RestIdx j) : AddCommMonoid (SumFamily A j i) := by
  rcases i with (_ | x) <;> infer_instance

instance (j : ι) (i : Unit ⊕ RestIdx j) : Module ℚ_[p] (SumFamily A j i) := by
  rcases i with (_ | x) <;> infer_instance

def splitFamilyEquiv (i : Unit ⊕ RestIdx j) :
    A ((splitEquiv j).symm i) ≃ₗ[ℚ_[p]] SumFamily A j i := by
  rcases i with (_ | x)
  · exact LinearEquiv.refl ℚ_[p] (A j)
  · exact LinearEquiv.refl ℚ_[p] (A x.1)

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

/-- Actual split equivalence E ≃ A_j (x) Rest. -/
def splitTensorEquiv :
    (⨂[ℚ_[p]] (i : ι), A i) ≃ₗ[ℚ_[p]]
      TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) :=
  (PiTensorProduct.reindex ℚ_[p] A (splitEquiv j)).trans
    ((PiTensorProduct.congr (splitFamilyEquiv (p := p) A j)).trans
      ((PiTensorProduct.tmulEquivDep ℚ_[p] (SumFamily A j)).symm.trans
        (TensorProduct.congr
          (PiTensorProduct.subsingletonEquiv (R := ℚ_[p]) (s := fun _ : Unit => A j) ())
          (LinearEquiv.refl ℚ_[p] (Rest (p := p) A j)))))

/-- Binary action mult(g) on A_j and identity on Rest. -/
def binaryAction (g : A j) :
    TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) →ₗ[ℚ_[p]]
      TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) :=
  TensorProduct.map (LinearMap.mulLeft ℚ_[p] g) LinearMap.id

/-- Actual pure-tensor action: multiplication by 1 (x) ... (x) g (x) ... (x) 1. -/
def tensorActionMul (g : A j) :
    (⨂[ℚ_[p]] (i : ι), A i) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] (i : ι), A i) :=
  LinearMap.mulLeft ℚ_[p]
    (PiTensorProduct.tprod ℚ_[p] (fun i => if h : i = j then h ▸ g else 1))

/-- Actual action compatibility: the pure-tensor action corresponds to
mult(g) (x) id under the explicit split equivalence. -/
theorem splitTensorEquiv_action (g : A j) :
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


/-- Actual determinant after the split: det(action) = Norm(g)^dim(Rest). -/
theorem tensorDet_eq_norm_pow_finrank (g : A j) :
    LinearMap.det (tensorActionMul (p := p) A j g) =
      (Algebra.norm ℚ_[p] g) ^ Module.finrank ℚ_[p] (Rest (p := p) A j) := by
  let e := splitTensorEquiv (p := p) A j
  have hconj := splitTensorEquiv_action (p := p) A j g
  have hdet : LinearMap.det (tensorActionMul (p := p) A j g) =
      LinearMap.det (binaryAction (p := p) A j g) := by
    rw [← LinearMap.det_conj (tensorActionMul (p := p) A j g) e]
    have hfun : (↑e) ∘ₗ tensorActionMul (p := p) A j g ∘ₗ ↑e.symm =
        binaryAction (p := p) A j g := by
      apply LinearMap.ext
      intro x
      change e (tensorActionMul (p := p) A j g (e.symm x)) =
        binaryAction (p := p) A j g x
      have hx := LinearMap.congr_fun hconj (e.symm x)
      simpa [e] using hx
    rw [hfun]
  rw [hdet]
  change LinearMap.det
      (TensorProduct.map (LinearMap.mulLeft ℚ_[p] g) (LinearMap.id : Rest (p := p) A j →ₗ[ℚ_[p]] Rest (p := p) A j)) =
    (Algebra.norm ℚ_[p] g) ^ Module.finrank ℚ_[p] (Rest (p := p) A j)
  rw [EtaTensorDetProductActual.det_tensorProduct_map (Module.finBasis ℚ_[p] (A j))
    (Module.finBasis ℚ_[p] (Rest (p := p) A j))
    (LinearMap.mulLeft ℚ_[p] g) LinearMap.id]
  simp only [LinearMap.det_id, one_pow, Fintype.card_fin, mul_one]
  congr 1


/-- Actual combinatorial exponent: the complement tensor dimension is D/d_j. -/
theorem finrank_Rest_eq_totalDim_div (j : ι) :
    Module.finrank ℚ_[p] (Rest (p := p) A j) =
      totalDim (p := p) A / factorDim (p := p) A j := by
  have hrest : Module.finrank ℚ_[p] (Rest (p := p) A j) =
      ∏ i : RestIdx j, Module.finrank ℚ_[p] (A i) := by
    change Module.finrank ℚ_[p] (FinitePadicTensor (p := p) (fun i : RestIdx j => A i)) =
      ∏ i : RestIdx j, Module.finrank ℚ_[p] (A i)
    rw [finrank_finitePadicTensor]
  have hD : totalDim (p := p) A =
      factorDim (p := p) A j *
        ∏ i : RestIdx j, Module.finrank ℚ_[p] (A i) := by
    unfold totalDim factorDim
    rw [Finset.prod_eq_mul_prod_diff_singleton j]
    · congr 1
      rw [Finset.prod_subtype (p := fun x => x ≠ j) (Finset.univ \ {j}) (fun x => by simp)
        (fun i => Module.finrank ℚ_[p] (A i))]
    · intro hj
      simp at hj
  rw [hrest, hD]
  exact (Nat.mul_div_right (∏ i : RestIdx j, Module.finrank ℚ_[p] (A i))
    (Module.finrank_pos (R := ℚ_[p]) (M := A j))).symm

/-- Actual BPS determinant target with the combinatorial exponent D/d_j. -/
def TensorDetNormTarget (g : A j) : Prop :=
  LinearMap.det (tensorActionMul (p := p) A j g) =
    (Algebra.norm ℚ_[p] g) ^ (totalDim (p := p) A / factorDim (p := p) A j)


/-- Actual BPS determinant formula: det(pure-tensor action) = Norm(g)^(D/d_j). -/
theorem tensorDetNormTarget_actual (g : A j) :
    TensorDetNormTarget (p := p) A j g := by
  unfold TensorDetNormTarget
  rw [tensorDet_eq_norm_pow_finrank (p := p) A j g,
    finrank_Rest_eq_totalDim_div (p := p) A j]

end LeanFormal.IUT.N8Closure.EtaTensorSplitActual
