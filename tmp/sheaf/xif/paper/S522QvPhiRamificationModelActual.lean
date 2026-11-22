import tmp.sheaf.xif.paper.S518ULiftNatDivisorialAddMonoidActual
import tmp.sheaf.xif.paper.S511PhiCvCandidateActual
import Iut.Foundations.SourceFiniteStageModelFrobenioid
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S518ULiftNatDivisorialAddMonoidActual
universe u
variable {K : Type u} [Field K]
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
noncomputable def qvPhiRamificationModel
    (R : RamificationIndexData (K := K)) :
    DivisorialMonoidOn (Example32SmallBase K) (fun {_ _} f => IsIso f) where
  obj _ := uliftNatDivisorialAddMonoid.{u}
  pullback f := uliftNatMulLeft (R.e f).val
  pullback_id X := by
    apply AddMonoidHom.ext
    intro n
    apply ULift.ext
    have hid : (R.e (𝟙 X)).val = 1 := congrArg PNat.val (R.e_id X)
    change (R.e (𝟙 X)).val * n.down = n.down
    rw [hid, one_mul]
  pullback_comp f g := by
    apply AddMonoidHom.ext
    intro n
    apply ULift.ext
    have hcomp : (R.e (f ≫ g)).val = (R.e f).val * (R.e g).val :=
      congrArg PNat.val (R.e_comp f g)
    change (R.e (f ≫ g)).val * n.down =
      (R.e f).val * ((R.e g).val * n.down)
    rw [hcomp]
    ring
  characteristicallyInjective f := by
    exact uliftNatMulLeft_injective (R.e f).pos
  fsmPullbackIsIso f hf := by
    have hone : (R.e f).val = 1 := congrArg PNat.val (R.e_iso f hf)
    constructor
    · exact uliftNatMulLeft_injective (R.e f).pos
    · intro y
      refine ⟨y, ?_⟩
      apply ULift.ext
      change (R.e f).val * y.down = y.down
      rw [hone, one_mul]
structure QvPhiRamificationModelActual where
  ramification : RamificationIndexData (K := K)
  phi : DivisorialMonoidOn (Example32SmallBase K) (fun {_ _} f => IsIso f)
  phi_eq : phi = qvPhiRamificationModel (K := K) ramification
noncomputable def qvPhiRamificationModelOf
    (R : RamificationIndexData (K := K)) : QvPhiRamificationModelActual (K := K) where
  ramification := R
  phi := qvPhiRamificationModel (K := K) R
  phi_eq := rfl
end LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
