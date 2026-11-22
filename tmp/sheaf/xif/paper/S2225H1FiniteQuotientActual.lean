import tmp.sheaf.xif.paper.S2214H1MonoidActual
import Mathlib.Data.Fintype.Pi
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
namespace LeanFormal.IUT.XiFPaper.S2225H1FiniteQuotientActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- A finite quotient action with the quotient type as a parameter, avoiding
the instance-projection problem of S2220. -/
structure S2225FiniteQuotientAction (n : ℕ) (Q : Type) [Group Q] [Finite Q] where
  q : LocalAbsoluteGalois p →* Q
  q_surjective : Function.Surjective q
  actionQ : Q →* MulAut (S2145Coeff p n)
  compat : ∀ g, actionQ (q g) =
    ((S2196MuActionTower p).actn n).automorphism g
/-- The induced continuous action of the finite quotient. -/
noncomputable def S2225QuotientAction (n : ℕ) (Q : Type) [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [IsTopologicalGroup Q]
    (D : S2225FiniteQuotientAction p n Q) :
    Iut.ContinuousGroupAction Q (S2145Coeff p n) := by
  exact { automorphism := D.actionQ
          continuous_action := continuous_of_discreteTopology }
/-- For finite Q, the H^1 of the quotient action is finite. -/
theorem S2225QuotientH1_finite (n : ℕ) (Q : Type) [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [IsTopologicalGroup Q]
    (D : S2225FiniteQuotientAction p n Q) :
    Finite (Iut.ContinuousH1 (S2225QuotientAction p n Q D)) := by
  classical
  haveI : NeZero (Nat.factorial n) := ⟨Nat.factorial_ne_zero n⟩
  haveI : Finite (S2145Coeff p n) := inferInstance
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Fintype (S2145Coeff p n) := Fintype.ofFinite _
  haveI : Fintype (Q → S2145Coeff p n) := inferInstance
  haveI : Finite (Q → S2145Coeff p n) := Finite.of_fintype _
  haveI : Finite (Iut.ContinuousOneCocycle (S2225QuotientAction p n Q D)) :=
    Finite.of_injective (fun z : Iut.ContinuousOneCocycle
        (S2225QuotientAction p n Q D) => z.toFun)
      (fun z w h => by
        apply Iut.ContinuousOneCocycle.ext
        intro g
        exact congrFun h g)
  exact Finite.of_surjective (Quotient.mk _) Quotient.mk_surjective
/-- Exact missing: the comparison between the G_v-H^1 and the finite-quotient
H^1. -/
structure S2225FiniteQuotientH1Data (n : ℕ) (Q : Type) [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [IsTopologicalGroup Q]
    extends S2225FiniteQuotientAction p n Q where
  h1Equiv : S2204H1 p n ≃
    Iut.ContinuousH1 (S2225QuotientAction p n Q toS2225FiniteQuotientAction)
/-- Given the comparison, the level H^1 is finite. -/
theorem S2225FiniteH1OfQuotient (n : ℕ) (Q : Type) [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [IsTopologicalGroup Q]
    (D : S2225FiniteQuotientH1Data p n Q) :
    Finite (S2204H1 p n) :=
  haveI : Finite (Iut.ContinuousH1
      (S2225QuotientAction p n Q D.toS2225FiniteQuotientAction)) :=
    S2225QuotientH1_finite p n Q D.toS2225FiniteQuotientAction
  Finite.of_injective (fun x : S2204H1 p n => D.h1Equiv x)
    D.h1Equiv.injective
#check S2225FiniteQuotientAction
#check S2225QuotientAction
#check S2225QuotientH1_finite
#check S2225FiniteQuotientH1Data
#check S2225FiniteH1OfQuotient
end LeanFormal.IUT.XiFPaper.S2225H1FiniteQuotientActual
end
