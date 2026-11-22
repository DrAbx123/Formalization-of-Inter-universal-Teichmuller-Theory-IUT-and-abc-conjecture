/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! # A511 glue: consumers of the Cor 3.12 -> ABC bridge hull interface -/

noncomputable section

namespace LeanFormal.IUT.Objects.BridgeGlue

open LeanFormal.IUT

universe u

variable {D : Cor312ToABCBridgeInterface.{u}}

/-- The hull/log-volume interface carried by the bridge interface. -/
def bridgeHullInterface (D : Cor312ToABCBridgeInterface.{u}) :
    IQHullLogVolumeInterface D.carrier := D.hullData

/-- The image union log-volume is bounded by the hull log-volume (consumer of the
interface's monotonicity). -/
theorem bridge_imageSet_logVolume_le_hull (D : Cor312ToABCBridgeInterface.{u}) :
    D.hullData.logVolume D.hullData.imageSet ≤ D.hullData.logVolume D.hullData.hull :=
  IQHullLogVolumeInterface.imageSet_logVolume_le_hull D.hullData

/-- The hull log-volume is finite (Corollary 3.12 finiteness from the bridge interface). -/
theorem bridge_hull_logVolume_lt_top (D : Cor312ToABCBridgeInterface.{u}) :
    D.hullData.logVolume D.hullData.hull < ⊤ :=
  D.hullData.hull_logVolume_lt_top

/-- Same finiteness expressed on the bridge log-volume functional. -/
theorem bridge_hull_lt_top_of_interface (D : Cor312ToABCBridgeInterface.{u}) :
    (bridgeHullInterface D).logVolume (bridgeHullInterface D).hull < ⊤ := 
  (bridgeHullInterface D).hull_logVolume_lt_top

end LeanFormal.IUT.Objects.BridgeGlue
