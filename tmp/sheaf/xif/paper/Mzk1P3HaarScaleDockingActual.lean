/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchC3HaarScaleFormulaActual
import tmp.sheaf.xif.paper.Mzk1NativeFinitePlaceDictionaryActual

/-! # P3: c3HaarScale formula layer <-> native finite-place carrier -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3HaarScaleDockingActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1NormArchC3HaarScaleFormulaActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Formula-layer docking: for a number field F, the candidate factor is C_F times the
local unit product.  Native carrier/product is the named data; no C3 inhabitant. -/
structure NativeHaarScaleDocking (F : Type) [Field F] [NumberField F] where
  localUnitProduct : ℝ
  localUnitProduct_pos : 0 < localUnitProduct
  haarScale : ℝ
  haarScale_eq : haarScale = c3HaarScaleCandidate F localUnitProduct
def dockingRows : List (String × String) :=
  [ ("NativeHaarScaleDocking", "formula-layer docking with native local product"),
    ("c3HaarScaleCandidate", "C_F * localUnitProduct"),
    ("native product=1", "green in NativeFinitePlaceDictionary"),
    ("C3S1902 blockEquiv", "GAP") ]
theorem dockingRows_length : dockingRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3HaarScaleDockingActual
