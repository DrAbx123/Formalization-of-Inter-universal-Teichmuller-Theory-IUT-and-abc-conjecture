/-!
# S3139: stage4 unit-map seam record (first-triangle route residual)

Data-only record for the stage4 canonical global-units-to-local-units map used
by the C2 finite-place channel: S3136LGPGlobalUnitsToLocalUnitsActual
(src 3949 D5877884 / olean 78352 A6DFFFC3) provides

* lgpGlobalUnitsToLocalUnits (C3 : SourcePilotRegionData I) (i : C3.tensorIndex) :
    (I.initial.arithmetic.Fmod)^x ->* (Completion (c3LogShellPlace C3 i))^x
* lgpGlobalUnitsToLocalUnits_apply, lgpC3Fiber_eq_completion,
* LGPGlobalUnitsLocalMissing/Gap {sameCIdentification, placeSelection,
  frobeniusCompatibility, reciprocalImageCompatibility};

and S3136LGPGlobalUnitsToBadPlaceUnitsActual provides the bad-place analogue
(lgpGlobalUnitsToBadPlaceUnits, lgpGlobalUnitsToBadPlaceAlgClosed, ...).

The seam into the first-triangle route composition is: given M0 (same-C
identification of the completion units with the prime-strip local units) and M1
(place selection), the stage4 map yields the C2 local element map
(@S3139C2LocalDegreeDataActual.SourceFmodLocalElementMap@) and hence the
finite-place copy action.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.FirstTriangleStage4SeamActual

/-- The stage4 seam of the first-triangle route residual. -/
structure SourceStage4UnitMapSeam where
  /-- the stage4 canonical unit map is available at the needed fiber -/
  unitMap : Prop
  /-- its realified degree readout is available (for the copy scalar) -/
  degreeReadout : Prop

/-- The exact stage4 constant names consumed by this stream (data only). -/
def stage4UnitMapNames : List (String × String) :=
  [ ("lgpGlobalUnitsToLocalUnits", "S3136LGPGlobalUnitsToLocalUnitsActual"),
    ("lgpGlobalUnitsToLocalUnits_apply", "S3136LGPGlobalUnitsToLocalUnitsActual"),
    ("lgpC3Fiber_eq_completion", "S3136LGPGlobalUnitsToLocalUnitsActual"),
    ("LGPGlobalUnitsLocalMissing", "S3136LGPGlobalUnitsToLocalUnitsActual"),
    ("lgpGlobalUnitsToBadPlaceUnits", "S3136LGPGlobalUnitsToBadPlaceUnitsActual"),
    ("lgpGlobalUnitsToBadPlaceAlgClosed", "S3136LGPGlobalUnitsToBadPlaceUnitsActual") ]

end LeanFormal.IUT.XiFPaper.FirstTriangleStage4SeamActual
