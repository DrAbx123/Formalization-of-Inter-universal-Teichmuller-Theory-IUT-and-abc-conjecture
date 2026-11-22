import tmp.sheaf.xif.paper.S2471M4G1Actual
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
open LeanFormal.IUT.XiFPaper.S2471M4G1Actual
namespace LeanFormal.IUT.XiFPaper.S2473M4G1Interfaces

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact G1 first missing beyond `muHatComparison`: the comparison must
intertwine the actual muHatZ action with the actual PsiCns action. -/
structure S2473G1EquivariantComparisonRequired where
  comparison : muHatComparison p
  equivariance : S2471G1EquivarianceRequired p comparison

/-- Conditional actual G1 data from the exact equivariant comparison. -/
noncomputable def S2473G1TopologicalModuleOf
    (E : S2473G1EquivariantComparisonRequired p) :
    S2046G1TopologicalModuleData p :=
  S2471G1TopologicalModuleOf p E.comparison E.equivariance

/-- Exact topology/continuity missing for G1. -/
structure S2473G1ContinuousActionRequired where
  top : TopologicalSpace (muHatZ p)
  continuous_action :
    letI := top
    Continuous (fun q : Gv p × muHatZ p =>
      S2471MuHatAction p q.1 q.2)

/-- Exact M4 normalization data missing. -/
abbrev S2473M4NormalizationRequired : Type :=
  S2136M4NormalizationData p

/-- M4 normalization proposition, unchanged. -/
abbrev S2473M4NormalizationProp : Prop :=
  PsiCnsKummerNormalization p

end LeanFormal.IUT.XiFPaper.S2473M4G1Interfaces
end
