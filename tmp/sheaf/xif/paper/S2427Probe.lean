import Mathlib.GroupTheory.Perm.Cycle.Type
noncomputable section
set_option maxHeartbeats 4000000
namespace Probe2427b

theorem cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  have hperm : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun x : β => (rfl : x = x))).symm) := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype (h := (rfl : b = b)), Equiv.permCongr_apply]
    rfl
  rw [hperm]
  exact Equiv.Perm.cycleType_extendDomain _

#print axioms cycleType_permCongr
end Probe2427b
