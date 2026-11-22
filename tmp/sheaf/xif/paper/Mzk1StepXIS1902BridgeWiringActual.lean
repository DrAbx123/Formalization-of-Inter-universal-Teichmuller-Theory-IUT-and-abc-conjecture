import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap1ConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi concrete bridge wiring

A bridge family carrying the explicit Gap-1 objects and named Gap-2 inputs, wired
through the green `bridgeInterfaceOfGap1Consumer`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual

universe u

structure StepXIBridgeFamily (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) where
  gap1 : ∀ ε : Real, 0 < ε → Gap1DataFamily W logShellPoint ε
  gap2 : ∀ ε : Real, 0 < ε → Gap2NamedInput W logShellPoint ε

def stepxiBridgeInterface (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIBridgeFamily X W logShellPoint) :
    Cor312ToABCBridgeInterface :=
  bridgeInterfaceOfGap1Consumer W logShellPoint I.gap1 I.gap2

theorem stepxiBridge_heightBound (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIBridgeFamily X W logShellPoint) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  heightBound_of_gap1Consumer W logShellPoint I.gap1 I.gap2

end LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeWiringActual

end
