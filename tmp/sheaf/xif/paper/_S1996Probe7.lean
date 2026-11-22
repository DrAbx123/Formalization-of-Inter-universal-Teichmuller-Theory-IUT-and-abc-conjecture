import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Tactic.Group

noncomputable section
namespace T
variable {M : Type*} [CommGroup M]

def mulRightEquiv (c : M) : M ≃ M where
  toFun x := x * c
  invFun x := x * c⁻¹
  left_inv x := by simp
  right_inv x := by simp

noncomputable def transportedCommGroup (c : M) : CommGroup M :=
  (mulRightEquiv c).symm.commGroup

noncomputable def decorationMulEquiv (c : M) :
    @MulEquiv M M (inferInstance : Mul M) ((transportedCommGroup c).toMul) where
  toFun u := u * c
  invFun u := u * c⁻¹
  left_inv u := by simp
  right_inv u := by simp
  map_mul' x y := by
    show (x * y) * c = (x * c) * c⁻¹ * (y * c)
    group

@[simp] theorem decorationMulEquiv_apply (c u : M) :
    decorationMulEquiv c u = u * c := rfl

end T
