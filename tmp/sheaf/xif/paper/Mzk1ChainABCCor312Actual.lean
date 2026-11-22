import tmp.sheaf.xif.paper.Mzk1BridgeInterfaceAssemblyActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractAssemblyActual
import tmp.sheaf.xif.paper.Mzk1E5UndilatedABCBridgeActualV2

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainABCCor312Actual — ABC and StepXI/Cor312 conjunction chains

Genuine new conjunctions: a per-epsilon comparison family yields ABCConjecture
while a StepXIContract yields the ordered Cor312Conclusion; likewise for the
undilated (b)+(c) route.  Combines the EXIT0 bridge assembly and StepXI assembly
consumers; no new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainABCCor312Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeActualV2

universe u

/-- Comparison family + StepXIContract -> ABC and ordered Cor312 conclusion. -/
theorem abc_and_cor312_of_family_and_contract (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (C : ∀ eps : ℝ, 0 < eps → Cor312EpsilonArithmeticComparison W eps)
    (q theta target : ℝ) (hq : q < 0) (hqt : q ≤ target) (htt : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt) :
    ABCConjecture ∧
      Cor312Conclusion (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt) :=
  ⟨abcConjecture_of_comparisonFamily X W C,
   cor312_of_constructed_stepXI (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt)⟩

/-- Undilated (b)+(c) + StepXIContract -> ABC and ordered Cor312 conclusion. -/
theorem abc_and_cor312_of_undilated_and_contract {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt)
    (q theta target : ℝ) (hq : q < 0) (hqt : q ≤ target) (htt : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt) :
    ABCConjecture ∧
      Cor312Conclusion (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt) :=
  ⟨abcConjecture_of_undilatedBounds hb hc,
   cor312_of_constructed_stepXI (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt)⟩

end LeanFormal.IUT.XiFPaper.Mzk1ChainABCCor312Actual

end
