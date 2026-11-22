import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap1ConsumerActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1/Gap2 assembly

Constructs the per-eps `HeightRegionGap1Data` from the proved height-object wiring
and an explicit height comparison, then assembles the green bridge interface with the
named Gap-2 input. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual

universe u

structure StepXIGap1Input (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real) where
  height_le_region : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

def StepXIGap1Input.toHeightRegionGap1Data (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real)
    (I : StepXIGap1Input X W logShellPoint epsilon) :
    HeightRegionGap1Data W logShellPoint epsilon where
  heightData := fun a b c h => heightRegionGap1Data_object a b c h
  thetaBound := thetaBoundOfHull W
  thetaBound_eq := thetaBoundOfHull_eq W
  height_le_normalizedRegionVolume := I.height_le_region

structure StepXIGapFamily (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) where
  gap1 : ∀ ε : Real, 0 < ε → StepXIGap1Input X W logShellPoint ε
  gap2 : ∀ ε : Real, 0 < ε → Gap2NamedInput W logShellPoint ε

def stepxiBridgeOfGaps (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) :
    Cor312ToABCBridgeInterface :=
  bridgeInterfaceOfGap1Consumer W logShellPoint
    (fun ε hε => (I.gap1 ε hε).toHeightRegionGap1Data X W logShellPoint ε)
    I.gap2

theorem stepxiBridgeOfGaps_heightBound (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  heightBound_of_gap1Consumer W logShellPoint
    (fun ε hε => (I.gap1 ε hε).toHeightRegionGap1Data X W logShellPoint ε)
    I.gap2

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual

end
