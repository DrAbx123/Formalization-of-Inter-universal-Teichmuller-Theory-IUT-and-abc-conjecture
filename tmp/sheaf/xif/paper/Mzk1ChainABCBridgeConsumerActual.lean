import tmp.sheaf.xif.paper.Mzk1BridgeInterfaceAssemblyActual
import tmp.sheaf.xif.paper.Mzk1E5UndilatedABCBridgeActualV2
import tmp.sheaf.xif.paper.Mzk1TargetABCInterfaceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainABCBridgeConsumerActual — chained ABC bridge consumers

Chains EXIT0 assets: comparison-family -> bridge -> ABC/height bound, and
undilated (b)+(c) -> ABC, plus the pointwise ABC target-data bound.  No new
math; named inputs explicit; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainABCBridgeConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeActualV2
open LeanFormal.IUT.XiFPaper.Mzk1TargetABCInterfaceActual

universe u

/-- Comparison family -> ABC via the assembled bridge. -/
theorem chain_abc_of_comparisonFamily (X : Type u) (W : IQHullLogVolumeInterface X)
    (C : ∀ eps : ℝ, 0 < eps → Cor312EpsilonArithmeticComparison W eps) :
    ABCConjecture :=
  abcConjecture_of_comparisonFamily X W C

/-- Undilated (b)+(c) bounds -> ABC. -/
theorem chain_abc_of_undilated {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  abcConjecture_of_undilatedBounds hb hc

/-- Pointwise ABC target-data height bound. -/
theorem chain_target_height_le {X : Type u} (d : ABCTargetData X) (x : X) :
    d.height x ≤ d.weight x + d.bound :=
  d.height_le x

def chainABCBridgeRows : List (String × String × String) :=
  [ ("comparison -> ABC", "chain_abc_of_comparisonFamily", "PROVED (reuse)"),
    ("undilated -> ABC", "chain_abc_of_undilated", "PROVED (reuse)"),
    ("target height bound", "chain_target_height_le", "PROVED (reuse)"),
    ("scope", "named inputs explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainABCBridgeRows_length : chainABCBridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainABCBridgeConsumerActual

end
