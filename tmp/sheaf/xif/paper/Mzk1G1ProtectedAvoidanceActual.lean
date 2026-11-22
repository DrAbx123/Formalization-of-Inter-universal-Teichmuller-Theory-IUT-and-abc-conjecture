import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedAvoidanceActual

/-- Actual protected-avoidance selection: a term outside a finite protected set. -/
noncomputable def protectedAvoidance {K : Type*} [Field K] [Infinite K]
    (protectedSet : Finset K) : { t : K // t ∉ protectedSet } :=
  ⟨Classical.choose (Infinite.exists_notMem_finset protectedSet),
    Classical.choose_spec (Infinite.exists_notMem_finset protectedSet)⟩

theorem protectedAvoidance_spec {K : Type*} [Field K] [Infinite K]
    (protectedSet : Finset K) :
    (protectedAvoidance protectedSet).1 ∉ protectedSet :=
  (protectedAvoidance protectedSet).2

#print axioms protectedAvoidance_spec
end LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedAvoidanceActual