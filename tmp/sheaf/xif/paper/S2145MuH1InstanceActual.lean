import tmp.sheaf.xif.paper.S2142ActualH1TowerActual
import Mathlib.RingTheory.RootsOfUnity.Basic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT.XiFPaper.S2142ActualH1TowerActual
namespace LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The corrected divisibility-chain coefficient tower: mu_{n!}, not mu_n.
The consecutive tower mu_n has no nontrivial transition mu_{n+1} -> mu_n;
the paper's compatible system uses a divisibility chain. -/
abbrev S2145Coeff (n : ℕ) : Type :=
  rootsOfUnity (Nat.factorial n) (AlgebraicClosure ℚ_[p])
instance S2145Coeff_top (n : ℕ) : TopologicalSpace (S2145Coeff p n) := ⊥
instance S2145Coeff_discrete (n : ℕ) : DiscreteTopology (S2145Coeff p n) :=
  discreteTopology_bot _
instance S2145Coeff_topGroup (n : ℕ) : IsTopologicalGroup (S2145Coeff p n) :=
  {}
/-- The actual power transition mu_{(n+1)!} -> mu_{n!}, zeta |-> zeta^(n+1). -/
noncomputable def S2145PowMap (n : ℕ) :
    S2145Coeff p (n+1) →* S2145Coeff p n where
  toFun ζ := ⟨ζ.1 ^ (n+1), by
    rw [mem_rootsOfUnity]
    rw [← pow_mul]
    have hfac : (n+1) * Nat.factorial n = Nat.factorial (n+1) :=
      (Nat.factorial_succ n).symm
    rw [hfac]
    exact ζ.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_pow]
/-- The corrected tower has finite level values. -/
theorem S2145Coeff_finite (n : ℕ) : Finite (S2145Coeff p n) := by
  haveI : NeZero (Nat.factorial n) := ⟨Nat.factorial_ne_zero n⟩
  infer_instance
/-- Exact first missing: the corrected tower's transition surjectivity. -/
def S2145TransitionSurjective (n : ℕ) : Prop :=
  Function.Surjective (S2145PowMap p n)
/-- Exact first missing: a continuous action of G_v on the corrected
coefficient tower, compatible with the power transitions. -/
structure S2145MuActionTower where
  actn : ∀ n, Iut.ContinuousGroupAction
    (LocalAbsoluteGalois p) (S2145Coeff p n)
  compat : ∀ n (g : LocalAbsoluteGalois p) (ζ : S2145Coeff p (n+1)),
    (S2145PowMap p n) ((actn (n+1)).act g ζ) =
      (actn n).act g ((S2145PowMap p n) ζ)
/-- Exact first missing: the actual S2142 tower instantiated with mu_{n!}. -/
structure S2145ActualMuH1Instance extends S2145MuActionTower p where
  finiteH1 : ∀ n, Finite (Iut.ContinuousH1 (actn n))
  proj : ∀ n, Iut.ContinuousH1 (actn (n+1)) →*
    Iut.ContinuousH1 (actn n)
  proj_surjective : ∀ n, Function.Surjective (proj n)
/-- An actual instance gives the S2142 tower. -/
noncomputable def S2145ToS2142 (A : S2145ActualMuH1Instance p) :
    S2142ActualMuH1Tower where
  p := p
  hprime := inferInstance
  coeff := S2145Coeff p
  commGroupCoeff := fun n => inferInstance
  topCoeff := fun n => inferInstance
  discreteCoeff := fun n => inferInstance
  topGroupCoeff := fun n => inferInstance
  actn := A.actn
  finiteH1 := A.finiteH1
  proj := A.proj
  proj_surjective := A.proj_surjective
#check S2145Coeff
#check S2145PowMap
#check S2145Coeff_finite
#check S2145TransitionSurjective
#check S2145MuActionTower
#check S2145ActualMuH1Instance
#check S2145ToS2142
end LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
end
