import tmp.sheaf.xif.paper.S2150MuTransitionActual
import LeanFormal.IUT.IUTII.Kummer.LocalGaloisKummerAction
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2150MuTransitionActual
namespace LeanFormal.IUT.XiFPaper.S2164MuActionTowerActual
variable (p : Nat) [Fact (Nat.Prime p)]
abbrev S2164Roots (n : ℕ) : Subgroup ((AlgebraicClosure ℚ_[p])ˣ) :=
  rootsOfUnity (Nat.factorial n) (AlgebraicClosure ℚ_[p])
/-- The units automorphism preserves the mu_{n!} subgroup. -/
theorem S2164Roots_map (n : ℕ) (e : (AlgebraicClosure ℚ_[p])ˣ ≃* (AlgebraicClosure ℚ_[p])ˣ) :
    (S2164Roots p n).map (e : (AlgebraicClosure ℚ_[p])ˣ →* (AlgebraicClosure ℚ_[p])ˣ) =
      S2164Roots p n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ^ Nat.factorial n = 1 := hy
    change (e y) ^ Nat.factorial n = 1
    rw [← map_pow, hy', map_one]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    have hx' : x ^ Nat.factorial n = 1 := hx
    change (e.symm x) ^ Nat.factorial n = 1
    rw [← map_pow, hx', map_one]
/-- The actual automorphism of mu_{n!} induced by a units automorphism. -/
noncomputable def S2164RootsMulAut (n : ℕ)
    (e : (AlgebraicClosure ℚ_[p])ˣ ≃* (AlgebraicClosure ℚ_[p])ˣ) :
    MulAut (S2164Roots p n) :=
  (e.subgroupMap (S2164Roots p n)).trans
    (MulEquiv.subgroupCongr (S2164Roots_map p n e))
/-- The actual action homomorphism of G_v on mu_{n!}. -/
noncomputable def S2164RootsActionAut (n : ℕ) :
    LocalAbsoluteGalois p →* MulAut (S2164Roots p n) where
  toFun σ := S2164RootsMulAut p n (localGaloisUnitsAction p σ)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
/-- Compatibility of the action with the power transition. -/
theorem S2164PowMap_equivariant (n : ℕ) (σ : LocalAbsoluteGalois p)
    (ζ : S2164Roots p (n+1)) :
    S2145PowMap p n (S2164RootsActionAut p (n+1) σ ζ) =
      S2164RootsActionAut p n σ (S2145PowMap p n ζ) := by
  apply Subtype.ext
  simp [S2164RootsActionAut, S2164RootsMulAut, S2145PowMap, map_pow]
/-- Continuity of the restricted action at level n (exact missing input). -/
def S2164ActionContinuous (n : ℕ) : Prop :=
  Continuous fun q : LocalAbsoluteGalois p × S2164Roots p n =>
    S2164RootsActionAut p n q.1 q.2
/-- Given continuity at every level, the actual S2145 action tower is obtained. -/
noncomputable def S2164MuActionTowerOfContinuous
    (h : ∀ n, S2164ActionContinuous p n) : S2145MuActionTower p where
  actn n :=
    { automorphism := S2164RootsActionAut p n
      continuous_action := h n }
  compat := fun n g ζ => S2164PowMap_equivariant p n g ζ
#check S2164RootsMulAut
#check S2164RootsActionAut
#check S2164PowMap_equivariant
#check S2164ActionContinuous
#check S2164MuActionTowerOfContinuous
end LeanFormal.IUT.XiFPaper.S2164MuActionTowerActual
end
