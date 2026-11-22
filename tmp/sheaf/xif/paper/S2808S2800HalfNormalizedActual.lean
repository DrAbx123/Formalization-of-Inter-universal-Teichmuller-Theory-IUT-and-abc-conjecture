import tmp.sheaf.xif.paper.S2800LineBundleCor312BridgeActual
import tmp.sheaf.xif.paper.S2781PointedLineBundleRegionActual
import tmp.sheaf.xif.paper.S2792NormalizedLineBundleBridge
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped ENNReal nonZeroDivisors Classical
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual

variable (l : PrimeGeFive)

/-- The point covolume log used for the half-normalized interface. -/
noncomputable def S2808CovolumeLog (y : S2800Carrier l) : Real :=
  S2781CovolumeLog l y

/-- Half-normalized log-volume: supremum over points of half the point covolume log. -/
noncomputable def S2808LogVolume (S : Set (S2800Carrier l)) : ENNReal :=
  ⨆ y : S, ENNReal.ofReal ((1 / 2) * S2808CovolumeLog l y.1)

theorem S2808LogVolume_mono {S T : Set (S2800Carrier l)} (hST : S ⊆ T) :
    S2808LogVolume l S <= S2808LogVolume l T := by
  refine iSup_le fun y : S => ?_
  exact le_iSup (fun z : T => ENNReal.ofReal ((1 / 2) * S2808CovolumeLog l z.1))
    ⟨y.1, hST y.2⟩

theorem S2808LogVolume_singleton_lt_top (x : S2800Carrier l) :
    S2808LogVolume l ({x} : Set (S2800Carrier l)) < ⊤ := by
  refine lt_of_le_of_lt ?_
    (ENNReal.ofReal_lt_top (r := (1 / 2) * S2808CovolumeLog l x))
  refine iSup_le fun y => ?_
  have hy : y.1 = x := Set.mem_singleton_iff.mp y.2
  rw [hy]

/-- Half-normalized IQ-hull on the line-bundle carrier. -/
noncomputable def S2808HalfIQHull (x0 : S2800Carrier l) :
    IQHullLogVolumeInterface (S2800Carrier l) where
  imageSet := {x0}
  hull := {x0}
  imageSet_subset_hull := subset_rfl
  logVolume := S2808LogVolume l
  logVolume_mono := by
    intro S T hST
    exact S2808LogVolume_mono l hST
  unitRegion := {x0}
  scaleShift := id
  hull_subset_scaleShift := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  unitRegion_logVolume_lt_top := S2808LogVolume_singleton_lt_top l x0
  scaleShift_unitRegion_logVolume_le := by
    rw [Set.image_id]

/-- Concrete half-normalized global data. -/
noncomputable def S2808Global : S2800GlobalData l where
  covolume := S2808CovolumeLog l
  W := S2808HalfIQHull l 1
  logShellPoint := S2781LogShellPoint l
  W_logVolume_eq := fun S => rfl

end LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
end
