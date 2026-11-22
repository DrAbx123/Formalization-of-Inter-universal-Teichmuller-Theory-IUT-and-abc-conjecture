import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Ext
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
    @MulEquiv M M (inferInstance : Mul M) ((transportedCommGroup c).toMul) :=
  MulEquiv.mk (mulRightEquiv c) (by
    intro x y
    show (x * y) * c = (x * c) * c⁻¹ * (y * c)
    group)

@[simp] theorem decorationMulEquiv_apply (c u : M) :
    decorationMulEquiv c u = u * c := rfl

example (c : M) : transportedCommGroup c = (inferInstance : CommGroup M) := by
  apply CommGroup.ext
  ext x y
  show x * c⁻¹ * y = x * y
  rfl

end T
