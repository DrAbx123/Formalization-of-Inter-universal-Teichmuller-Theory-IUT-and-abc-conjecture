import Iut.Foundations.SourceFiniteStageModelFrobenioid
import tmp.sheaf.xif.paper.S432SmallModelActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S516ULiftNatPhiActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
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
      (stageDivisorGrothendieckEquivInt : Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) equality
    have mappedEquality' :
        multiple.1 • (stageDivisorGrothendieckEquivInt : Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) value =
          (divisor.down : ℤ) := by
      simpa only [map_nsmul, stageDivisorGrothendieckEquivInt_of] using
        mappedEquality.symm
    have valueNonnegative :
        0 ≤ (stageDivisorGrothendieckEquivInt : Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) value := by
      apply (nsmul_nonneg_iff (Nat.ne_of_gt multiple.2)).mp
      rw [mappedEquality']
      exact Int.natCast_nonneg divisor.down
    refine ⟨ULift.up (Int.toNat
      ((stageDivisorGrothendieckEquivInt : Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ) value)), ?_⟩
    apply (stageDivisorGrothendieckEquivInt : Algebra.GrothendieckAddGroup (ULift.{u+1} ℕ) ≃+ ℤ).injective
    rw [stageDivisorGrothendieckEquivInt_of]
    exact Int.toNat_of_nonneg valueNonnegative

/-- Multiplication by e on ULift Nat. -/
noncomputable def uliftNatMulLeft (e : ℕ) :
    ULift.{u+1} ℕ →+ ULift.{u+1} ℕ where
  toFun (n : ULift.{u+1} ℕ) := ULift.up (e * n.down)
  map_zero' := by
    apply ULift.ext
    simp
  map_add' x y := by
    apply ULift.ext
    simp [Nat.mul_add]

theorem uliftNatMulLeft_injective {e : ℕ} (he : 0 < e) :
    Function.Injective (uliftNatMulLeft e) := by
  intro x y h
  apply ULift.down_injective
  have h' : e * x.down = e * y.down := by
    simpa [uliftNatMulLeft] using congrArg ULift.down h
  exact Nat.mul_left_cancel he h'

/-- Explicit ramification-index interface for the Qv-Phi model. -/
structure QvRamificationIndexData (K : Type u) [Field K] where
  index : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → ℕ
  index_pos : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), 0 < index f
  index_id : ∀ X : Example32SmallBase K, index (𝟙 X) = 1
  index_comp : ∀ {X Y Z : Example32SmallBase K} (f : X ⟶ Y) (g : Y ⟶ Z),
    index (f ≫ g) = index f * index g
  index_iso : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), IsIso f → index f = 1

/-- Qv-Phi ramification model: obj Nat, pullback n ↦ e(f) n. -/
noncomputable def qvPhiRamificationModel
    {K : Type u} [Field K] (E : QvRamificationIndexData K) :
    DivisorialMonoidOn (Example32SmallBase K) (fun {_ _} f => IsIso f) where
  obj _ := uliftNatDivisorialAddMonoid.{u}
  pullback f := uliftNatMulLeft (E.index f)
  pullback_id X := by
    ext n
    change E.index (𝟙 X) * n.down = n.down
    rw [E.index_id]
    simp
  pullback_comp f g := by
    ext n
    change E.index (f ≫ g) * n.down = E.index f * (E.index g * n.down)
    rw [E.index_comp, Nat.mul_assoc]
  characteristicallyInjective f := by
    exact uliftNatMulLeft_injective (E.index_pos f)
  fsmPullbackIsIso f hf := by
    have hpos : 0 < E.index f := E.index_pos f
    have hone : E.index f = 1 := E.index_iso f hf
    constructor
    · exact uliftNatMulLeft_injective hpos
    · intro y
      refine ⟨y, ?_⟩
      change uliftNatMulLeft (E.index f) y = y
      rw [hone]
      change ULift.up (1 * y.down) = y
      apply ULift.ext
      simp

end LeanFormal.IUT.XiFPaper.S516ULiftNatPhiActual

end
