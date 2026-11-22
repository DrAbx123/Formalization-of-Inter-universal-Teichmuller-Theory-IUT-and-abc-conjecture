import tmp.sheaf.xif.paper.S2145MuH1InstanceActual
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
namespace LeanFormal.IUT.XiFPaper.S2150MuTransitionActual
variable (p : Nat) [Fact (Nat.Prime p)]
theorem S2150Transition_surjective (n : ℕ) :
    Function.Surjective (S2145PowMap p n) := by
  intro y
  classical
  let G1 := S2145Coeff p (n+1)
  let G0 := S2145Coeff p n
  haveI : NeZero (Nat.factorial (n+1)) := ⟨Nat.factorial_ne_zero _⟩
  haveI : NeZero (Nat.factorial n) := ⟨Nat.factorial_ne_zero _⟩
  haveI : HasEnoughRootsOfUnity (AlgebraicClosure ℚ_[p]) (Nat.factorial (n+1)) :=
    inferInstance
  haveI : HasEnoughRootsOfUnity (AlgebraicClosure ℚ_[p]) (Nat.factorial n) :=
    inferInstance
  have hcard1 : Nat.card G1 = Nat.factorial (n+1) := by
    dsimp [G1, S2145Coeff]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity _ _
  have hcard0 : Nat.card G0 = Nat.factorial n := by
    dsimp [G0, S2145Coeff]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity _ _
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := G1)
  let η : G0 := S2145PowMap p n ζ
  have hordζ : orderOf ζ = Nat.factorial (n+1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, hcard1]
  have hordζunits : orderOf (ζ : (AlgebraicClosure ℚ_[p])ˣ) =
      Nat.factorial (n+1) := by
    have hc := Subgroup.orderOf_coe (G := (AlgebraicClosure ℚ_[p])ˣ) (H := rootsOfUnity (Nat.factorial (n+1)) (AlgebraicClosure ℚ_[p])) (a := ζ)
    rw [hc, hordζ]
  have hηcoe : (η : (AlgebraicClosure ℚ_[p])ˣ) =
      (ζ : (AlgebraicClosure ℚ_[p])ˣ) ^ (n+1) := rfl
  have hordη : orderOf η = Nat.factorial n := by
    have hc0 := Subgroup.orderOf_coe (G := (AlgebraicClosure ℚ_[p])ˣ) (H := rootsOfUnity (Nat.factorial n) (AlgebraicClosure ℚ_[p])) (a := η)
    rw [← hc0, hηcoe, orderOf_pow' (x := (ζ : (AlgebraicClosure ℚ_[p])ˣ)) (n := n+1) (Nat.succ_ne_zero n), hordζunits]
    have hdvd : (n+1) ∣ Nat.factorial (n+1) :=
      Nat.dvd_factorial (Nat.succ_pos n) (le_refl (n+1))
    rw [Nat.gcd_eq_right hdvd]
    rw [Nat.factorial_succ, Nat.mul_comm]
    exact Nat.mul_div_left (Nat.factorial n) (Nat.succ_pos n)
  have htop : Subgroup.zpowers η = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hordη, hcard0]
  have hy : y ∈ Subgroup.zpowers η := by
    rw [htop]
    exact Subgroup.mem_top y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨ζ ^ k, ?_⟩
  rw [← hk, map_zpow]
#check S2150Transition_surjective
end LeanFormal.IUT.XiFPaper.S2150MuTransitionActual
end
