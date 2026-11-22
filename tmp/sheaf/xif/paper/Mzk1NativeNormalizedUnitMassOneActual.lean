/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-! # #10: normalized unit mass = 1 — exact GAP record

Attempt: rescale `rootExtensionHaar` by the local unit-ball mass to get
`normalizedRootExtensionHaar` with unit-ball mass 1, then product over Bad.
Blocked: `rootNormedExtension T b` is an `IntermediateField`, not a plain
`Type` with a registered `MeasurableSpace`/`SigmaFinite` instance in this
context; `Measure.pi` then cannot be formed.  The scalar normalization
`c_b = rootExtensionHaar(unitBall)` is available (pos/finite), but the
measure-level normalized product is not packaged.
No axiom/sorry. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassOneActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Local unit-ball scalar whose normalization would make the local unit mass 1. -/
noncomputable def localUnitMassScalar (b : Bad (nativePlaceSelection T)) : ℝ≥0∞ :=
  rootExtensionHaar T b (rootExtensionUnitBall T b)

theorem localUnitMassScalar_pos (b : Bad (nativePlaceSelection T)) :
    0 < localUnitMassScalar (T := T) b :=
  rootExtensionUnitBall_measure_pos (T := T) (b := b)

theorem localUnitMassScalar_lt_top (b : Bad (nativePlaceSelection T)) :
    localUnitMassScalar (T := T) b < ⊤ :=
  rootExtensionUnitBall_measure_lt_top (T := T) (b := b)

def normalizedUnitMassRows : List (String × String) :=
  [ ("localUnitMassScalar", "green: local unit-ball mass, pos/finite"),
    ("normalizedRootExtensionHaar", "GAP: rootNormedExtension lacks MeasurableSpace/SigmaFinite instance"),
    ("normalized unit mass=1", "GAP: measure-level product not formed"),
    ("actual s1915UnitMass", "additive product; =1 needs normalized comparison") ]
theorem normalizedUnitMassRows_length : normalizedUnitMassRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassOneActual
