import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! # Mzk1Stage4S1902InterfaceBridgeConnectionActual (stage4 lane; unique filename)

A617 module: connects the GREEN concrete S1902 interface (`s1902IQHullLogVolumeInterface`)
to the generic Cor 3.12 -> ABC bridge interface and to the concrete comparison-region
evidence.  Supplementary evidence only: the canonical bridge interface is mainline's
`Mzk1S1902BridgeInterfaceActual`, which this file does not modify.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902InterfaceBridgeConnectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.ABCBridge

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The green concrete S1902 interface's image set lies in its hull. -/
theorem s1902Interface_image_subset_hull :
    (s1902IQHullLogVolumeInterface T).imageSet ⊆ (s1902IQHullLogVolumeInterface T).hull :=
  (s1902IQHullLogVolumeInterface T).imageSet_subset_hull

/-- The green concrete S1902 interface's log-volume is monotone. -/
theorem s1902Interface_logVolume_mono {S U : Set (S1902Carrier T)} (h : S ⊆ U) :
    (s1902IQHullLogVolumeInterface T).logVolume S ≤ (s1902IQHullLogVolumeInterface T).logVolume U :=
  (s1902IQHullLogVolumeInterface T).logVolume_mono h

/-- Generic bridge consumer: any Cor 3.12 -> ABC bridge interface gives the ABC-style
height bound (restated from the green bridge theorem). -/
theorem bridge_heightBound (D : Cor312ToABCBridgeInterface) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound D

#check s1902Interface_image_subset_hull
#check s1902Interface_logVolume_mono
#check bridge_heightBound

end LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902InterfaceBridgeConnectionActual
end
