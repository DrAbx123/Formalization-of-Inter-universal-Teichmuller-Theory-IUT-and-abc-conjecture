import tmp.sheaf.xif.paper.S2419H1SurjLimitActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open KummerTheory
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2210H1FiniteActual
open LeanFormal.IUT.XiFPaper.S2213H1QuotientActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2390H1ComparisonDoneActual
open LeanFormal.IUT.XiFPaper.S2399H1QuotientActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
open LeanFormal.IUT.XiFPaper.S2419H1SurjLimitActual
namespace LeanFormal.IUT.XiFPaper.S2425H1SurjInternal
variable (p : Nat) [Fact (Nat.Prime p)]
local instance s2425MulDistrib (n : ℕ) :
    MulDistribMulAction (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  MulDistribMulAction.compHom (S2145Coeff p n)
    ((S2196MuActionTower p).actn n).automorphism
/-- The factorial divisibility `n! ∣ (n+1)!`. -/
theorem S2425FactDvd (n : ℕ) : Nat.factorial n ∣ Nat.factorial (n+1) :=
  ⟨n+1, by rw [Nat.factorial_succ, mul_comm]⟩
/-- The quotient `(n+1)! / n! = n+1`. -/
theorem S2425FactDvd_div (n : ℕ) : Nat.factorial (n+1) / Nat.factorial n = n + 1 := by
  rw [Nat.factorial_succ, Nat.mul_div_left _ (Nat.factorial_pos n)]
/-- The actual power transition is the Kummer transition `ζ ↦ ζ^((n+1)!/n!)`. -/
theorem S2425PowMap_eq_transition (n : ℕ) (ζ : S2145Coeff p (n+1)) :
    S2145PowMap p n ζ = KummerTheory.Mu.transition (S2425FactDvd n) ζ := by
  apply Subtype.ext
  change ζ.1 ^ (n+1) = ζ.1 ^ (Nat.factorial (n+1) / Nat.factorial n)
  rw [S2425FactDvd_div]
/-- The external cocycle map underlying `h1Transition` is the internal coefficient
pushforward. -/
theorem S2425CocycleSquare (n : ℕ)
    (w : Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn (n+1))) :
    S2390ToExternalCocycle p n (S2210CochainPushforward p n w) =
      ContH1.cocyclesMap (MonoidHom.id (LocalAbsoluteGalois p)) continuous_id
        (KummerTheory.Mu.transition (S2425FactDvd n))
        continuous_of_discreteTopology
        (fun σ ζ => KummerTheory.Mu.transition_smul (S2425FactDvd n) σ ζ)
        (S2390ToExternalCocycle p (n+1) w) := by
  apply Subtype.ext
  funext σ
  rw [ContH1.cocyclesMap_apply]
  exact S2425PowMap_eq_transition p n (w σ)
/-- The alignment square: under the internal/external H1 equivalence, the internal
level transition corresponds to the external Kummer transition. -/
theorem S2425Square (n : ℕ) (z : S2204H1 p (n+1)) :
    S2399ToExternal p n (S2213H1Pushforward p n z) =
      KummerTheory.h1Transition (K := ℚ_[p]) (Ω := AlgebraicClosure ℚ_[p])
        (m := Nat.factorial n) (n := Nat.factorial (n+1)) (S2425FactDvd n)
        (S2399ToExternal p (n+1) z) := by
  refine Quotient.inductionOn z ?_
  intro w
  show ContH1.mk (S2390ToExternalCocycle p n (S2210CochainPushforward p n w)) =
    KummerTheory.h1Transition (K := ℚ_[p]) (Ω := AlgebraicClosure ℚ_[p])
      (m := Nat.factorial n) (n := Nat.factorial (n+1))
      (S2425FactDvd n) (ContH1.mk (S2390ToExternalCocycle p (n+1) w))
  rw [KummerTheory.h1Transition, ContH1.map_mk]
  exact congrArg ContH1.mk (S2425CocycleSquare p n w)
/-- The internal level transition is surjective. -/
theorem S2425H1Surjective (p : Nat) [Fact (Nat.Prime p)] :
    ∀ n, Function.Surjective (⇑(S2214H1PushforwardHom p n)) := by
  intro n y
  haveI hm : NeZero (Nat.factorial n : ℚ_[p]) :=
    ⟨by exact_mod_cast Nat.factorial_ne_zero n⟩
  haveI hn : NeZero (Nat.factorial (n+1) : ℚ_[p]) :=
    ⟨by exact_mod_cast Nat.factorial_ne_zero (n+1)⟩
  obtain ⟨x', hx'⟩ := S2419H1Transition_surjective p (Nat.factorial n)
    (Nat.factorial (n+1)) (S2425FactDvd n) ((S2410H1Equiv p n) y)
  refine ⟨(S2410H1Equiv p (n+1)).symm x', ?_⟩
  apply (S2410H1Equiv p n).injective
  show S2399ToExternal p n
      (S2213H1Pushforward p n ((S2410H1Equiv p (n+1)).symm x')) =
    S2399ToExternal p n y
  rw [S2425Square p n ((S2410H1Equiv p (n+1)).symm x')]
  have hx : S2399ToExternal p (n+1) ((S2410H1Equiv p (n+1)).symm x') = x' :=
    (S2410H1Equiv p (n+1)).apply_symm_apply x'
  rw [hx]
  exact hx'
/-- The full remaining H1 data of S2214, from the surjectivity and finiteness. -/
noncomputable def S2425H1RemainingData : S2214H1RemainingData p where
  finiteH1 := fun n => S2410FiniteH1 p n
  proj_surjective := S2425H1Surjective p
/-- The actual S2204 H1 instance data. -/
noncomputable def S2425ToS2204H1InstanceData : S2204H1InstanceData p :=
  S2214ToS2204H1InstanceData p (S2425H1RemainingData p)
/-- The actual S2145 instance. -/
noncomputable def S2425ToS2145Instance : S2145ActualMuH1Instance p :=
  S2214ToS2145Instance p (S2425H1RemainingData p)
#check S2425H1Surjective
#print axioms S2425H1Surjective
#print axioms S2425ToS2145Instance
end LeanFormal.IUT.XiFPaper.S2425H1SurjInternal
end
