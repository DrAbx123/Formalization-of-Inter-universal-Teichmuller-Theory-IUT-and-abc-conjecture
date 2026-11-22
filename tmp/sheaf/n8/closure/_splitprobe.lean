import tmp.sheaf.n8.closure.EtaTensorDetProductActual
import tmp.sheaf.n8.closure.EtaTensorBlockDetActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open scoped TensorProduct

namespace Probe
universe u
variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

abbrev RestIdx := {i : ι // i ≠ j}
abbrev Rest := ⨂[ℚ_[p]] (i : RestIdx j), A i

/-- Index equivalence i <-> Unit + {i // i ≠ j}. -/
def splitEquiv : ι ≃ Unit ⊕ RestIdx j where
  toFun i := if h : i = j then Sum.inl () else Sum.inr ⟨i, h⟩
  invFun s := Sum.rec (fun _ => j) (fun x => x.1) s
  left_inv i := by
    by_cases h : i = j
    · simp [h]
    · simp [h]
  right_inv s := by
    rcases s with (_ | x)
    · simp
    · simp [x.2]

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

/-- Actual linear equivalence E ≃ A_j (x) Rest. -/
def splitTensorEquiv :
    TensorBlock (p := p) A ≃ₗ[ℚ_[p]]
      TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) :=
  (PiTensorProduct.reindex ℚ_[p] A (splitEquiv j)).trans
    ((PiTensorProduct.congr (splitFamilyEquiv (p := p) A j)).trans
      ((PiTensorProduct.tmulEquivDep ℚ_[p] (SumFamily A j)).symm.trans
        (TensorProduct.congr
          (PiTensorProduct.subsingletonEquiv (R := ℚ_[p]) (s := fun _ : Unit => A j) ())
          (LinearEquiv.refl ℚ_[p] (Rest (p := p) A j)))))

#check splitTensorEquiv


def binaryAction (j : ι) (g : A j) :
    TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) →ₗ[ℚ_[p]]
      TensorProduct ℚ_[p] (A j) (Rest (p := p) A j) :=
  TensorProduct.map (LinearMap.mulLeft ℚ_[p] g) LinearMap.id

example (j : ι) (g : A j) :
    (splitTensorEquiv (p := p) A j).toLinearMap.comp
        (tensorAction (p := p) A j g) =
      (binaryAction (p := p) A j g).comp
        (splitTensorEquiv (p := p) A j).toLinearMap := by
  apply PiTensorProduct.ext
  ext x
  let e : TensorBlock (p := p) A := PiTensorProduct.tprod ℚ_[p] x
  change splitTensorEquiv (p := p) A j (tensorAction (p := p) A j g e) =
    binaryAction (p := p) A j g (splitTensorEquiv (p := p) A j e)
  change splitTensorEquiv (p := p) A j
      ((LinearMap.mul ℚ_[p] (TensorBlock (p := p) A)) (tensorUnit (p := p) A j g) e) = _
  rw [show e = PiTensorProduct.tprod ℚ_[p] x from rfl]
  rw [PiTensorProduct.tprod_mul_tprod]
  simp [splitTensorEquiv, binaryAction, tensorAction, tensorUnit,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply_apply, PiTensorProduct.tprod_mul_tprod, PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.subsingletonEquiv_apply_tprod,
    TensorProduct.congr_tmul, TensorProduct.map_tmul]
