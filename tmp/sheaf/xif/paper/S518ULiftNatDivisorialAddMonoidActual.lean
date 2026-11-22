import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-! # S518: DivisorialAddMonoid on ULift ℕ

Independent construction.  Integral and sharp are transported from ℕ via the
additive equivalence AddEquiv.ulift (stageDivisorEquivNat); saturated is proved
through the actual Grothendieck-group equivalence with ℤ. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S518ULiftNatDivisorialAddMonoidActual

open Iut
open Iut.SourceFinitePlaceReconstruction

universe u

/-- ULift Nat as a DivisorialAddMonoid at universe u+1. -/
noncomputable def uliftNatDivisorialAddMonoid :
    DivisorialAddMonoid.{u+1} where
  carrier := ULift.{u+1} ℕ
  integral := by
    intro first second third equality
    apply ULift.down_injective
    exact Nat.add_left_cancel (congrArg ULift.down equality)
  sharp := by
    intro value hypothesis
    apply ULift.down_injective
    exact Nat.isAddUnit_iff.mp
      (hypothesis.map (stageDivisorEquivNat : ULift.{u+1} ℕ ≃+ ℕ).toAddMonoidHom)
  saturated := by
    intro value multiple hypothesis
    obtain ⟨divisor, equality⟩ := hypothesis
    have mappedEquality := congrArg
      (stageDivisorGrothendieckEquivInt :
        Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) equality
    have mappedEquality' :
        multiple.1 • (stageDivisorGrothendieckEquivInt :
          Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) value =
          (divisor.down : ℤ) := by
      simpa only [map_nsmul, stageDivisorGrothendieckEquivInt_of] using
        mappedEquality.symm
    have valueNonnegative :
        0 ≤ (stageDivisorGrothendieckEquivInt :
          Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) value := by
      apply (nsmul_nonneg_iff (Nat.ne_of_gt multiple.2)).mp
      rw [mappedEquality']
      exact Int.natCast_nonneg divisor.down
    refine ⟨ULift.up (Int.toNat
      ((stageDivisorGrothendieckEquivInt :
        Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) value)), ?_⟩
    apply (stageDivisorGrothendieckEquivInt :
      Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ).injective
    rw [stageDivisorGrothendieckEquivInt_of]
    exact Int.toNat_of_nonneg valueNonnegative

end LeanFormal.IUT.XiFPaper.S518ULiftNatDivisorialAddMonoidActual

end
