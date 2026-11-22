import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedAvoidanceFinalActual

/-- Final consumer: actual protected-avoidance selection. -/
noncomputable def protectedAvoidanceFinal {K : Type*} [Field K] [Infinite K]
    (protectedSet : Finset K) : { t : K // t ∉ protectedSet } :=
  ⟨Classical.choose (Infinite.exists_notMem_finset protectedSet),
    Classical.choose_spec (Infinite.exists_notMem_finset protectedSet)⟩

theorem protectedAvoidanceFinal_spec {K : Type*} [Field K] [Infinite K]
    (protectedSet : Finset K) :
    (protectedAvoidanceFinal protectedSet).1 ∉ protectedSet :=
  (protectedAvoidanceFinal protectedSet).2

#print axioms protectedAvoidanceFinal_spec
end LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedAvoidanceFinalActual