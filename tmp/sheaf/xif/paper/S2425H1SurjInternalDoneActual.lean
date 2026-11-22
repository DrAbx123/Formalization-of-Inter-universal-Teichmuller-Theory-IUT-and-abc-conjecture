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
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2384H1ComparisonActual
open LeanFormal.IUT.XiFPaper.S2390H1ComparisonDoneActual
open LeanFormal.IUT.XiFPaper.S2399H1QuotientActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
open LeanFormal.IUT.XiFPaper.S2419H1SurjLimitActual
namespace LeanFormal.IUT.XiFPaper.S2425H1SurjInternalDoneActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2425MulDistrib :
    MulDistribMulAction (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  MulDistribMulAction.compHom (S2145Coeff p n)
    ((S2196MuActionTower p).actn n).automorphism
theorem S2425FactDvd (n : Nat) :
    Nat.factorial n ∣ Nat.factorial (n+1) :=
  Nat.factorial_dvd_factorial (Nat.le_succ n)
theorem S2425FactDiv (n : Nat) :
    Nat.factorial (n+1) / Nat.factorial n = n+1 := by
  rw [Nat.factorial_succ]
  exact Nat.mul_div_left (n+1) (Nat.factorial_pos n)
theorem S2425MuTransition_eq
    (ζ : S2145Coeff p (n+1)) :
    KummerTheory.Mu.transition (S2425FactDvd n) ζ =
      S2145PowMap p n ζ := by
  apply Subtype.ext
  change ζ.1 ^ (Nat.factorial (n+1) / Nat.factorial n) = ζ.1 ^ (n+1)
  rw [S2425FactDiv]
theorem S2425Square_cocycle
    (z : Iut.ContinuousOneCocycle
      ((S2196MuActionTower p).actn (n+1))) :
    S2390ToExternalCocycle p n
        (S2210CochainPushforward p n z) =
      ContH1.cocyclesMap
        (MonoidHom.id (LocalAbsoluteGalois p)) continuous_id
        (KummerTheory.Mu.transition (S2425FactDvd n))
        continuous_of_discreteTopology
        (fun σ ζ => KummerTheory.Mu.transition_smul
          (S2425FactDvd n) σ ζ)
        (S2390ToExternalCocycle p (n+1) z) := by
  apply Subtype.ext
  funext g
  change S2145PowMap p n (z.toFun g) =
    KummerTheory.Mu.transition (S2425FactDvd n)
      ((S2390ToExternalCocycle p (n+1) z).1 g)
  rw [S2425MuTransition_eq]
  rfl
/-- The external Kummer transition at factorial levels. -/
noncomputable abbrev S2425H1Transition :
    ContH1 Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])
        (KummerTheory.Mu (Nat.factorial (n+1))
          (AlgebraicClosure ℚ_[p])) →*
      ContH1 Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])
        (KummerTheory.Mu (Nat.factorial n)
          (AlgebraicClosure ℚ_[p])) :=
  KummerTheory.h1Transition (K := ℚ_[p])
    (Ω := AlgebraicClosure ℚ_[p]) (S2425FactDvd n)
/-- The alignment square: the internal power transition corresponds to the
end
