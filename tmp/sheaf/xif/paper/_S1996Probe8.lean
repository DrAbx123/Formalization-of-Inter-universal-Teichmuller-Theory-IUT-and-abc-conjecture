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

example : transportedCommGroup (1 : M) = (inferInstance : CommGroup M) := by
  apply CommGroup.ext
  ext x y
  rw [Equiv.mul_def]
  simp [mulRightEquiv]

end T
