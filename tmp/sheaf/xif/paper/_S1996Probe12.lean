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

example (c x y : M) :
    (letI := (mulRightEquiv c).symm.mul; x * y) = x * c⁻¹ * y := by
  change (letI := (mulRightEquiv c).symm.mul; x * y) = x * c⁻¹ * y
  rw [Equiv.mul_def]
  simp [mulRightEquiv]
  group

end T
