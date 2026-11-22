import tmp.sheaf.xif.paper.S511PhiCvCandidateActual
import tmp.sheaf.xif.paper.S515NatDivisorialMonoidULiftActual
import Iut.Foundations.SourceFiniteStageModelFrobenioid

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S519QvPhiRamificationModelActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open Iut.SourceFinitePlaceReconstruction

universe u
variable {K : Type u} [Field K]

/-- Actual ULift Nat divisorial monoid at universe u+1. -/
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
      (hypothesis.map (stageDivisorEquivNat).toAddMonoidHom)
  saturated := by
    intro value multiple hypothesis
    obtain ⟨divisor, equality⟩ := hypothesis
    have mappedEquality := congrArg
      (stageDivisorGrothendieckEquivInt) equality
    have mappedEquality' :
        multiple.1 • stageDivisorGrothendieckEquivInt value =
          (divisor.down : ℤ) := by
      simpa only [map_nsmul, stageDivisorGrothendieckEquivInt_of] using
        mappedEquality.symm
    have valueNonnegative :
        0 ≤ stageDivisorGrothendieckEquivInt value := by
      apply (nsmul_nonneg_iff (Nat.ne_of_gt multiple.2)).mp
      rw [mappedEquality']
      exact Int.natCast_nonneg divisor.down
    refine ⟨ULift.up (Int.toNat
      (stageDivisorGrothendieckEquivInt value)), ?_⟩
    apply (stageDivisorGrothendieckEquivInt).injective
    rw [stageDivisorGrothendieckEquivInt_of]
    exact Int.toNat_of_nonneg valueNonnegative

noncomputable def uliftNatMulLeft (e : ℕ) :
    ULift.{u+1} ℕ →+ ULift.{u+1} ℕ where
  toFun n := ULift.up (e * n.down)
  map_zero' := rfl
  map_add' x y := by
    apply ULift.ext
    simp [Nat.mul_add]

theorem uliftNatMulLeft_injective {e : ℕ} (he : 0 < e) :
    Function.Injective (uliftNatMulLeft e) := by
  intro x y h
  apply ULift.down_injective
  have h' := congrArg ULift.down h
  simpa [uliftNatMulLeft] using Nat.mul_left_cancel he h'

noncomputable def actualQvPhiRamificationModel
    (R : RamificationIndexData (K := K)) :
    DivisorialMonoidOn (Example32SmallBase K) (fun {_ _} f => IsIso f) where
  obj _ := uliftNatDivisorialAddMonoid.{u}
  pullback f := uliftNatMulLeft (R.e f).val
  pullback_id X := by
    ext n
    have hid : (R.e (𝟙 X)).val = 1 := congrArg PNat.val (R.e_id X)
    rw [hid]
    simp [uliftNatMulLeft]
    rfl
  pullback_comp f g := by
    ext n
    have hcomp : (R.e (f ≫ g)).val = (R.e f).val * (R.e g).val :=
      congrArg PNat.val (R.e_comp f g)
    rw [hcomp]
    simp [uliftNatMulLeft, Nat.mul_assoc]
    rfl
  characteristicallyInjective f := by
    exact uliftNatMulLeft_injective (R.e f).pos
  fsmPullbackIsIso f hf := by
    have hone : (R.e f).val = 1 := congrArg PNat.val (R.e_iso f hf)
    constructor
    · exact uliftNatMulLeft_injective (R.e f).pos
    · intro y
      refine ⟨y, ?_⟩
      apply ULift.ext
      rw [hone]
      simp [uliftNatMulLeft]
      rfl

structure QvPhiRamificationModelActual where
  ramification : RamificationIndexData (K := K)
  phi : DivisorialMonoidOn (Example32SmallBase K) (fun {_ _} f => IsIso f)
  phi_eq : phi = actualQvPhiRamificationModel (K := K) ramification

noncomputable def qvPhiRamificationModelOf
    (R : RamificationIndexData (K := K)) : QvPhiRamificationModelActual (K := K) where
  ramification := R
  phi := actualQvPhiRamificationModel (K := K) R
  phi_eq := rfl

end LeanFormal.IUT.XiFPaper.S519QvPhiRamificationModelActual

end
