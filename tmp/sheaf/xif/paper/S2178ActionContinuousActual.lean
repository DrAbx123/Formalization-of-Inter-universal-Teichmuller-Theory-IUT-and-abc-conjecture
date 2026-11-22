import tmp.sheaf.xif.paper.S2164MuActionTowerActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2164MuActionTowerActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
namespace LeanFormal.IUT.XiFPaper.S2178ActionContinuousActual
variable (p : Nat) [Fact (Nat.Prime p)]
local instance s2178UnitsTop : TopologicalSpace ((AlgebraicClosure ℚ_[p])ˣ) := ⊥
local instance s2178UnitsDisc : DiscreteTopology ((AlgebraicClosure ℚ_[p])ˣ) :=
  discreteTopology_bot _
/-- The topology bridge needed for the restricted action: the declared
S2145Coeff topology on mu_{n!} must be identified with the subtype topology
inherited from the units action. -/
def S2178TopologyBridge (n : ℕ) : Prop :=
  (S2145Coeff_top p n : TopologicalSpace (S2164Roots p n)) =
    instTopologicalSpaceSubtype
theorem S2178TopologyBridge_holds (n : ℕ) :
    S2178TopologyBridge p n := by
  unfold S2178TopologyBridge
  apply TopologicalSpace.ext
  funext s
  simp [S2145Coeff_top, instTopologicalSpaceSubtype]
/-- The exact continuity obligation for the restricted G_v-action. -/
def S2178ActionContinuousRequired (n : ℕ) : Prop :=
  S2164ActionContinuous p n
#check S2178TopologyBridge
#check S2178TopologyBridge_holds
#check S2178ActionContinuousRequired
end LeanFormal.IUT.XiFPaper.S2178ActionContinuousActual
end
