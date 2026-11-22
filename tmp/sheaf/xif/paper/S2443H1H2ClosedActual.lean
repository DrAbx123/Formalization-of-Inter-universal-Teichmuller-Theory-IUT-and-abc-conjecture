import tmp.sheaf.xif.paper.S2440H1H2IntegrationActual
import tmp.sheaf.xif.paper.S2441H2RepresentativeActual
import tmp.sheaf.xif.paper.S2442H2ComparisonActual2
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual
open LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual
open LeanFormal.IUT.XiFPaper.S2427H2CompatCleanActual
open LeanFormal.IUT.XiFPaper.S2441H2RepresentativeActual
open LeanFormal.IUT.XiFPaper.S2430H1FinalActual
open LeanFormal.IUT.XiFPaper.S2442H2ComparisonActual2
namespace LeanFormal.IUT.XiFPaper.S2443H1H2ClosedActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual S2114 compatible representative lift for the mu_{n!} tower. -/
noncomputable def S2443ActualCompatibleRepresentativeLift :
    S2114CompatibleRepresentativeLift (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat :=
  S2427ActualRepresentativeLift p
/-- The actual H^2 comparison is surjective. -/
theorem S2443ActualH2Comparison_surjective :
    Function.Surjective
      (h2Comparison (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn
        (S2196MuActionTower p).compat) :=
  S2427ActualH2Comparison_surjective p
/-- The actual H^2 comparison surjectivity in S2114 form. -/
theorem S2443ActualS2114H2Surjective :
    S2114H2ComparisonSurjective (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat :=
  S2427ActualS2114Surjective p
/-- The S2441 exact missing is now inhabited by the actual lift. -/
noncomputable def S2443S2441Lift :
    S2441ActualRepresentativeLiftRequired p :=
  ⟨S2443ActualCompatibleRepresentativeLift p⟩
/-- The H1 closure: lim^1 H^1 = 0 for the actual tower. -/
theorem S2443ActualH1Lim1_subsingleton :
    Subsingleton (S2426Lim1 (S2426ActualH1Tower p)) :=
  S2430ActualH1Lim1_subsingleton p
#check S2443ActualCompatibleRepresentativeLift
#check S2443ActualH2Comparison_surjective
#check S2443ActualS2114H2Surjective
#check S2443S2441Lift
#check S2443ActualH1Lim1_subsingleton
end LeanFormal.IUT.XiFPaper.S2443H1H2ClosedActual
end
