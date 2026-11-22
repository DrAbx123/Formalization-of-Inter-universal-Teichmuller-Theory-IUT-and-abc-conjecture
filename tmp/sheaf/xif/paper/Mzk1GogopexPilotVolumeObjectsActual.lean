/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison

/-! # A517: pilot-volume objects (Gogopex PilotComparison consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexPilotVolume

open Iut RealLineCopy

/-- A single pilot log-volume object: the tagged signed magnitude with its side/value
accessors. -/
structure PilotVolumeObject where
  /-- The underlying pilot log-volume. -/
  volume : PilotLogVolume

/-- The side tag of the pilot volume. -/
theorem PilotVolumeObject.side (D : PilotVolumeObject) : D.volume.side = D.volume.side := rfl

/-- Build a pilot volume from a side and a positive stored magnitude. -/
def pilotVolumeOf (side : PilotSide) (value : Real) : PilotVolumeObject where
  volume := { side := side, value := value }

theorem pilotVolumeOf_side (side : PilotSide) (value : Real) :
    (pilotVolumeOf side value).volume.side = side := rfl

theorem pilotVolumeOf_value (side : PilotSide) (value : Real) :
    (pilotVolumeOf side value).volume.value = value := rfl

/-- The two-pilot comparison object: theta/q pilot volumes together with the signed
Corollary 3.12 inequality between them. -/
structure PilotPairObject where
  /-- The Theta-pilot volume. -/
  theta : PilotLogVolume
  /-- The q-pilot volume. -/
  q : PilotLogVolume
  /-- The signed comparison. -/
  comparison : Corollary312Inequality theta q

/-- The pair object yields its stored signed comparison. -/
theorem PilotPairObject.comparison_holds (D : PilotPairObject) :
    Corollary312Inequality D.theta D.q := D.comparison

end LeanFormal.IUT.Objects.GogopexPilotVolume
