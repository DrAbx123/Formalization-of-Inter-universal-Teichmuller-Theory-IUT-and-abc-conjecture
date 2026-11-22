/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-!
# Mzk1LogShellTensorObjectActual — log-shell / tensor-packet object (3.11 object side)

A517: reference object reusing the green S1902 root-extension tensor construction:
* the tensor-packet unit region `O` (`rootExtensionProductUnitBall`);
* the least `λ·O` holomorphic hull of the actual Theta image
  (`rootExtensionProductImageHull`);
* the normalized Haar log-volume (`s1902NormalizedHaar`, `s1902LogVolume`);
* the compact hull facts (`s1902Hull_compact`, `s1902Hull_subset_unitRegion`).

No new axiom, no comparison, no interface. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellTensorObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The log-shell / tensor-packet object: unit region, hull, image, and Haar log-volume. -/
structure LogShellTensorObject where
  /-- the product unit region `1,circ U`. -/
  unitRegion : Set (S1902Carrier T)
  /-- the actual Theta image. -/
  imageSet : Set (S1902Carrier T)
  /-- the least `λ·O` hull of the image. -/
  hull : Set (S1902Carrier T)
  /-- the normalized Haar log-volume. -/
  logVolume : Set (S1902Carrier T) → ENNReal

/-- The constructed log-shell/tensor object from the green S1902 assets. -/
noncomputable def logShellTensorObject : LogShellTensorObject T where
  unitRegion := s1902UnitRegion T
  imageSet := s1902ImageSet T
  hull := s1902Hull T
  logVolume := s1902LogVolume T

/-- `_constructed`: unit region is the actual product unit ball. -/
theorem logShellTensorObject_unitRegion :
    (logShellTensorObject T).unitRegion = s1902UnitRegion T := rfl

/-- `_constructed`: hull is the actual least `λ·O` hull. -/
theorem logShellTensorObject_hull :
    (logShellTensorObject T).hull = s1902Hull T := rfl

/-- The actual Theta image is contained in the hull. -/
theorem logShellTensorObject_image_subset_hull :
    (logShellTensorObject T).imageSet ⊆ (logShellTensorObject T).hull :=
  s1902ImageSet_subset_hull T

/-- The hull is contained in the unit region `O`. -/
theorem logShellTensorObject_hull_subset_unitRegion :
    (logShellTensorObject T).hull ⊆ (logShellTensorObject T).unitRegion :=
  s1902Hull_subset_unitRegion T

/-- The hull is compact (finite product of compact closed balls). -/
theorem logShellTensorObject_hull_compact :
    IsCompact (logShellTensorObject T).hull :=
  s1902Hull_compact T

/-- The normalized Haar log-volume of the unit region is `1`. -/
theorem logShellTensorObject_logVolume_unitRegion :
    (logShellTensorObject T).logVolume (logShellTensorObject T).unitRegion = 1 :=
  s1902LogVolume_unitRegion T

/-- The log-volume is finite on the hull. -/
theorem logShellTensorObject_logVolume_hull_lt_top :
    (logShellTensorObject T).logVolume (logShellTensorObject T).hull < ⊤ :=
  s1902Hull_logVolume_lt_top T

#check logShellTensorObject_image_subset_hull
#check logShellTensorObject_hull_compact

end LeanFormal.IUT.XiFPaper.Mzk1LogShellTensorObjectActual
end
