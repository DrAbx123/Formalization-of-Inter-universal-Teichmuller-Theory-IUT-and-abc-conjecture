import tmp.sheaf.xif.paper.S2430H1FinalActual
import tmp.sheaf.xif.paper.S2427H2CompatCleanActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual
open LeanFormal.IUT.XiFPaper.S2427H2CompatCleanActual
open LeanFormal.IUT.XiFPaper.S2430H1FinalActual
namespace LeanFormal.IUT.XiFPaper.S2440H1H2IntegrationActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual S2145 H^1 instance assembled from the Kummer comparison. -/
noncomputable def S2440S2145Instance : S2145ActualMuH1Instance p :=
  S2430ActualS2145Instance p
/-- The actual H^1 tower and its Mittag-Leffler property. -/
theorem S2440MittagLeffler :
    Subsingleton (S2426Lim1 (S2426ActualH1Tower p)) :=
  S2430ActualH1Lim1_subsingleton p
/-- The actual H^2 compatible representative lift, as a real S2114 object. -/
noncomputable abbrev S2440CompatibleRepresentativeLift :=
  S2427ActualCompatibleRepresentativeLift p
/-- The actual H^2 comparison. -/
noncomputable abbrev S2440H2Comparison :=
  S2427ActualH2Comparison p
/-- Exact missing: an actual H^2 compatible representative lift. -/
def S2440CompatibleRepresentativeLiftRequired : Prop :=
  Nonempty (S2440CompatibleRepresentativeLift p)
/-- Exact missing: surjectivity of the actual H^2 comparison. -/
def S2440H2ComparisonSurjectiveRequired : Prop :=
  Function.Surjective (S2440H2Comparison p)
/-- The two exact missing formulations are equivalent (S2114). -/
theorem S2440_required_iff :
    S2440H2ComparisonSurjectiveRequired p ↔
      S2440CompatibleRepresentativeLiftRequired p :=
  S2427ActualH2Comparison_surjective_iff_nonempty p
#check S2440S2145Instance
#check S2440MittagLeffler
#check S2440CompatibleRepresentativeLift
#check S2440H2Comparison
#check S2440CompatibleRepresentativeLiftRequired
#check S2440H2ComparisonSurjectiveRequired
#check S2440_required_iff
end LeanFormal.IUT.XiFPaper.S2440H1H2IntegrationActual
end
