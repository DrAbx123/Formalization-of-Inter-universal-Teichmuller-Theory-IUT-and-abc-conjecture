import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

noncomputable section
namespace T
variable {M : Type*} [CommGroup M]

def mulRightEquiv (c : M) : M ≃ M where
  toFun x := x * c
  invFun x := x * c⁻¹
  left_inv x := by simp
  right_inv x := by simp

@[reducible] noncomputable def transportedMul (c : M) : Mul M :=
  (mulRightEquiv c).symm.mul

noncomputable def transportedCommGroup (c : M) : CommGroup M :=
  (mulRightEquiv c).symm.commGroup

noncomputable def decorationMulEquiv (c : M) :
    @MulEquiv M M (inferInstance : Mul M) (transportedMul c) :=
  @MulEquiv.mk M M (inferInstance : Mul M) (transportedMul c)
    (mulRightEquiv c) (by
      intro x y
      change (mulRightEquiv c) (x * y) =
        (letI := transportedMul c; (mulRightEquiv c) x * (mulRightEquiv c) y)
      rw [Equiv.mul_def]
      simp [mulRightEquiv])

@[simp] theorem decorationMulEquiv_apply (c u : M) :
    decorationMulEquiv c u = u * c := rfl

noncomputable def transportedAction {G : Type*} [Group G] (c : M) (rho : G →* @MulAut M inferInstance) (g : G) :
    @MulAut M (transportedMul c) :=
  @MulEquiv.trans M M M (transportedMul c) (inferInstance : Mul M) (transportedMul c)
    (@MulEquiv.symm M M (inferInstance : Mul M) (transportedMul c) (decorationMulEquiv c))
    (@MulEquiv.trans M M M (inferInstance : Mul M) (inferInstance : Mul M) (transportedMul c)
      (rho g) (decorationMulEquiv c))

example {G : Type*} [Group G] (c : M) (rho : G →* @MulAut M inferInstance) (g : G) (x : M) :
    transportedAction c rho g (decorationMulEquiv c x) = decorationMulEquiv c (rho g x) := by
  simp [transportedAction]
  change (decorationMulEquiv c).symm (decorationMulEquiv c x) = x
  exact (decorationMulEquiv c).symm_apply_apply x

end T
