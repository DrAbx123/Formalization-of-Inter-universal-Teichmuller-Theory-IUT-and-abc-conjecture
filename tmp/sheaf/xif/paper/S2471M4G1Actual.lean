import tmp.sheaf.xif.paper.S2442MuQZFinalActual
import tmp.sheaf.xif.paper.S2046G1CyclotomeActual
import tmp.sheaf.xif.paper.S2136M4KummerNormalizationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual
open LeanFormal.IUT.XiFPaper.S2136M4KummerNormalizationActual
open LeanFormal.IUT.XiFPaper.S2442MuQZFinalActual
namespace LeanFormal.IUT.XiFPaper.S2471M4G1Actual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Actual algebraic Gv-action on muHatZ from the actual muQZ action. -/
noncomputable abbrev S2471MuHatAction : Gv p →* MulAut (muHatZ p) :=
  S2442MuHatAction p

/-- Exact equivariance missing: under the (still missing) module comparison,
the actual muHatZ action must intertwine the actual PsiCns action. -/
def S2471G1EquivarianceRequired (h : muHatComparison p) : Prop :=
  ∀ (g : Gv p) (x : muHatZ p),
    S2046G1ModuleEquivOfComparison p h (S2471MuHatAction p g x) =
      S2046G1PsiCnsAction p g (S2046G1ModuleEquivOfComparison p h x)

/-- Conditional actual G1 module data: actual action plus the missing
comparison and equivariance. -/
noncomputable def S2471G1TopologicalModuleOf
    (h : muHatComparison p) (heq : S2471G1EquivarianceRequired p h) :
    S2046G1TopologicalModuleData p where
  muHatAction := S2471MuHatAction p
  equiv := S2046G1ModuleEquivOfComparison p h
  equivariant := heq

/-- Exact topology missing: a topology on muHatZ. -/
abbrev S2471MuHatTopologyRequired : Type := TopologicalSpace (muHatZ p)

/-- Exact continuous-action missing: topology, actual action, and joint
continuity. -/
structure S2471MuHatContinuousActionRequired where
  top : TopologicalSpace (muHatZ p)
  continuous_action :
    letI := top
    Continuous (fun q : Gv p × muHatZ p =>
      S2471MuHatAction p q.1 q.2)

/-- M4 exact normalization obligation, unchanged from S2136. -/
abbrev S2471M4NormalizationRequired : Prop :=
  PsiCnsKummerNormalization p

/-- M4 exact data structure. -/
abbrev S2471M4NormalizationData : Type :=
  S2136M4NormalizationData p

end LeanFormal.IUT.XiFPaper.S2471M4G1Actual
end
