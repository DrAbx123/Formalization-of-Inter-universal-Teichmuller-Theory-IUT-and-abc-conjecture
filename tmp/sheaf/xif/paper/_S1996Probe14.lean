import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Equiv.Defs

noncomputable section
namespace T
variable {G : Type*} [Group G]

example (α β : MulAut G) (x : G) :
    (MulAut.conj α β) (α x) = α (β x) := by
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.symm_apply_apply]

end T
