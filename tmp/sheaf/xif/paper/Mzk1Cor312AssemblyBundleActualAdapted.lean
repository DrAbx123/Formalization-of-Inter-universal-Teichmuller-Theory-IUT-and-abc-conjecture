import tmp.sheaf.xif.paper.Mzk1StepXIContractAssemblyActual
import tmp.sheaf.xif.paper.Mzk1BridgeInterfaceAssemblyActual
import tmp.sheaf.xif.paper.Mzk1Cor312BoundsActual
import tmp.sheaf.xif.paper.Mzk1TargetABCInterfaceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Cor312AssemblyBundleActualAdapted (adapted copy, A475 reuse) — Cor312/StepXI/ABC green-assembly bundle

Reuses EXIT0 assets: StepXI contract assembly, bridge-interface assembly,
Cor312 bounds bookkeeping and the ABC target-data interface.  No new math;
all named inputs remain explicit; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AssemblyBundleActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312BoundsActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetABCInterfaceActual

universe u

/-- StepXI contract from numeric source data (reuse). -/
def stepXIContract_of_data (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htt : target ≤ theta) {ipl she apt : Prop}
    (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract :=
  assembleStepXIContract q theta target hq hqt htt hipl hshe hapt

theorem cor312Conclusion_of_data (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htt : target ≤ theta) {ipl she apt : Prop}
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (stepXIContract_of_data q theta target hq hqt htt hipl hshe hapt) :=
  assembleStepXIContract_conclusion q theta target hq hqt htt hipl hshe hapt

/-- Bridge interface from a per-epsilon comparison family (reuse). -/
theorem nonempty_bridgeInterface_of_family (X : Type u) (W : IQHullLogVolumeInterface X)
    (h : ∀ eps : ℝ, 0 < eps → Cor312EpsilonArithmeticComparison W eps) :
    Nonempty Cor312ToABCBridgeInterface.{u} :=
  nonempty_bridgeInterface_of_comparisonFamily X W h

theorem abcConjecture_of_family (X : Type u) (W : IQHullLogVolumeInterface X)
    (h : ∀ eps : ℝ, 0 < eps → Cor312EpsilonArithmeticComparison W eps) :
    ABCConjecture :=
  abcConjecture_of_comparisonFamily X W h

theorem heightBound_of_family (X : Type u) (W : IQHullLogVolumeInterface X)
    (h : ∀ eps : ℝ, 0 < eps → Cor312EpsilonArithmeticComparison W eps) :
    ∀ eps : ℝ, 0 < eps → ∃ A : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A :=
  heightBound_of_comparisonFamily X W h

def cor312AssemblyRows : List (String × String × String) :=
  [ ("StepXI contract", "stepXIContract_of_data / cor312Conclusion_of_data", "PROVED (reuse)"),
    ("bridge/ABC", "nonempty_bridgeInterface_of_family / abcConjecture_of_family", "PROVED (reuse)"),
    ("height bound", "heightBound_of_family", "PROVED (reuse)"),
    ("scope", "inputs explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem cor312AssemblyRows_length : cor312AssemblyRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AssemblyBundleActualAdapted

end
