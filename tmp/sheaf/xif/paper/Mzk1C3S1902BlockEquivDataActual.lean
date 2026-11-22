/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.Mzk1C3S1902HaarScaleDataActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.n8.closure.SourcePilotRegion
import Mathlib.Tactic

/-! # #10 citizen: C3 block <-> S1902 blockEquiv data checklist (full names) -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902BlockEquivDataActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
universe u v
variable {l : PrimeGeFive} {V : Type v}
variable (I : LeanFormal.IUT.Theorem311Source.OriginalInput l V)
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (C3 : LeanFormal.IUT.N8Closure.SourcePilotRegion.SourcePilotRegionData I)

/-- Required citizen data for `C3S1902HaarScaleData.blockEquiv`:
index equivalence, per-fiber normed/ring equivalence, and assembled block equivalence.
No inhabitant is asserted. -/
structure C3S1902BlockEquivData where
  tensorIndexEquiv : C3.tensorIndex ≃ Bad (nativePlaceSelection T)
  fiberEquiv : ∀ i : C3.tensorIndex,
    LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual.C3LogShellFiber C3 i ≃
      LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual.rootNormedExtension T (tensorIndexEquiv i)
  blockEquiv : LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual.C3LogShellTensorBlock C3 ≃
    LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual.S1902Carrier T

def C3S1902BlockEquivDataRequired : Prop := Nonempty (C3S1902BlockEquivData I T C3)

/-- `unitMass` needed by `C3S1902HaarScaleData`: actual unit-region mass on the
S1902 carrier. -/
structure C3S1902UnitMassData where
  unitMass : ℝ
  unitMass_pos : 0 < unitMass
  unitMass_eq : unitMass =
    (LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual.rootExtensionProductHaar T
      (LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual.rootExtensionProductUnitBall T)).toReal

def C3S1902UnitMassDataRequired : Prop := Nonempty (C3S1902UnitMassData T)

def blockCitizenRows : List (String × String) :=
  [ ("tensorIndexEquiv", "C3.tensorIndex ≃ Bad (nativePlaceSelection T)"),
    ("fiberEquiv", "C3LogShellFiber ≃ rootNormedExtension"),
    ("blockEquiv", "C3LogShellTensorBlock ≃ S1902Carrier"),
    ("unitMass", "rootExtensionProductHaar unit-ball mass"),
    ("inhabitant", "GAP: not constructed") ]
theorem blockCitizenRows_length : blockCitizenRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3S1902BlockEquivDataActual
