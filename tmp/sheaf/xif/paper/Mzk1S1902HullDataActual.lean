import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

/-! # S1902 concrete `IQHullLogVolumeInterface` (supplementary thin re-export)

Ownership note (A615): canonical S1902 hull interface is hull lane's
`Mzk1S1902IQHullInterfaceActual`.  This file is a supplementary thin re-export of the
green `s1902IQHullLogVolumeInterface` in `S1902ActualThetaHullActual`; it does not
override the canonical file. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902HullDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Supplementary S1902 hull data: the green canonical actual interface instance. -/
noncomputable def s1902HullData :
    IQHullLogVolumeInterface (S1902Carrier T) :=
  s1902IQHullLogVolumeInterface T

theorem s1902HullData_hull :
    (s1902HullData T).hull = s1902Hull T := rfl

theorem s1902HullData_image :
    (s1902HullData T).imageSet = s1902ImageSet T := rfl

#print axioms s1902HullData_hull
#print axioms s1902HullData_image

end LeanFormal.IUT.XiFPaper.Mzk1S1902HullDataActual
