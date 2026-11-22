import Iut.Foundations.Frobenioid
import tmp.sheaf.xif.paper.S423NatDivisorialAddMonoidActual

/-! # S515: ULift nat divisorial monoid at universe u+1

S423's nat monoid has carrier ℕ : Type 0.  The ULift carrier is Type (u+1);
integral and sharp transport directly.  Saturation is the only field without
a ready-made ULift/Grothendieck transport lemma, so it is kept as an explicit
hypothesis in the conditional constructor; no fake proof is supplied.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S515NatDivisorialMonoidULiftActual

open Iut

universe u

/-- Saturation hypothesis for `ULift ℕ` at universe u+1. -/
def ULiftNatSaturated : Prop :=
  ∀ (x : Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ)) (n : ℕ+),
    n.1 • x ∈ Set.range
      (Algebra.GrothendieckAddGroup.of (M := ULift.{u+1} ℕ)) →
    x ∈ Set.range
      (Algebra.GrothendieckAddGroup.of (M := ULift.{u+1} ℕ))

/-- Conditional `DivisorialAddMonoid.{u+1}` with carrier `ULift ℕ`; integral
and sharp are transported, saturation is the explicit missing hypothesis. -/
noncomputable def dvNatDivisorialAddMonoidAtU
    (hsat : ULiftNatSaturated.{u}) :
    Iut.DivisorialAddMonoid.{u+1} where
  carrier := ULift.{u+1} ℕ
  integral := by
    intro a b c h
    apply ULift.ext
    exact Nat.add_left_cancel (congrArg ULift.down h)
  sharp := by
    intro a ha
    have h := IsAddUnit.map (AddEquiv.ulift : ULift.{u+1} ℕ ≃+ ℕ).toAddMonoidHom ha
    have hzero : (AddEquiv.ulift a : ℕ) = 0 :=
      LeanFormal.IUT.XiFPaper.S423NatDivisorialAddMonoidActual.natDivisorialAddMonoid.sharp _ h
    apply ULift.ext
    have hzero' : a.down = 0 := by
      simpa [AddEquiv.ulift] using hzero
    exact hzero'
  saturated := hsat

end LeanFormal.IUT.XiFPaper.S515NatDivisorialMonoidULiftActual
end
