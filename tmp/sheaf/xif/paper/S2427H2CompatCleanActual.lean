import tmp.sheaf.xif.paper.S2430H1FinalActual
import tmp.sheaf.xif.paper.S2114H2SurjectivityGapActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual
open LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual
namespace LeanFormal.IUT.XiFPaper.S2427H2CompatCleanActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual inverse limit of level H^2 groups. -/
noncomputable abbrev S2427ActualLimH2 :=
  S2426ActualLimH2 p
/-- The actual degree-two comparison. -/
noncomputable abbrev S2427ActualH2Comparison :=
  S2426ActualH2Comparison p
/-- The exact compatible representative lift for the actual coefficient
tower mu_{n!}. -/
noncomputable abbrev S2427ActualCompatibleRepresentativeLift :=
  S2426ActualCompatibleRepresentativeLift p
/-- Surjectivity of the actual H^2 comparison is exactly the nonemptiness of
the compatible representative lift. -/
theorem S2427ActualH2Comparison_surjective_iff_nonempty :
    Function.Surjective (S2427ActualH2Comparison p) ↔
      Nonempty (S2427ActualCompatibleRepresentativeLift p) := by
  constructor
  · intro h
    exact S2426ActualCompatibleRepresentativeLift_nonempty_of_surjective p h
  · rintro ⟨L⟩
    exact S2426ActualH2Comparison_surjective_of_lift p L
/-- Exact missing target: actual surjectivity of the H^2 comparison. -/
def S2427H2ComparisonSurjectiveRequired : Prop :=
  Function.Surjective (S2427ActualH2Comparison p)
/-- Exact missing target: an actual compatible representative lift. -/
def S2427CompatibleRepresentativeLiftRequired : Prop :=
  Nonempty (S2427ActualCompatibleRepresentativeLift p)
/-- The two exact missing formulations are equivalent. -/
theorem S2427_required_iff :
    S2427H2ComparisonSurjectiveRequired p ↔
      S2427CompatibleRepresentativeLiftRequired p :=
  S2427ActualH2Comparison_surjective_iff_nonempty p
#check S2427ActualLimH2
#check S2427ActualH2Comparison
#check S2427ActualCompatibleRepresentativeLift
#check S2427ActualH2Comparison_surjective_iff_nonempty
#check S2427H2ComparisonSurjectiveRequired
#check S2427CompatibleRepresentativeLiftRequired
end LeanFormal.IUT.XiFPaper.S2427H2CompatCleanActual
end
