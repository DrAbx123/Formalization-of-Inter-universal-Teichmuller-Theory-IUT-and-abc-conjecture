/-! Mainline: paper input index as Lean data (Mathlib-only documentation row list).
  Each row: paper input name, status, existing DAG node id, repo asset hint. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperInputIndexActual

/-- (paper input, status, DAG node id, repo asset). -/
def paperInputIndex : List (String × String × String × String) :=
  [ ("hCor312 (IUT IV sec2 gap1)", "NAMED", "iutiv-abc:N1", "Cor312ToABCBridgeInterface.height_le_normalizedRegionVolume"),
    ("hSlack (IUT IV sec2 gap2)", "NAMED", "iutiv-abc:N2", "Cor312ToABCBridgeInterface.regionVolume_le_normalizedWeight"),
    ("IUT IV sec1 display (Thm 1.10)", "CONDITIONAL", "iutiv-abc:IUTIV.S1.display", "S3171IUTIVSection1DisplayActual.thm110_final_display"),
    ("IUT IV (b) UndilatedHeightBound", "NAMED", "iutiv-abc:S3131.heightReduction", "S3131PaperRouteHeightReductionActual.UndilatedHeightBound"),
    ("IUT IV (c) UndilatedRegionBound", "NAMED", "iutiv-abc:S3131.regionReduction", "S3131PaperRouteRegionReductionActual.UndilatedRegionBound"),
    ("Thm 3.11 source inputs", "NAMED", "iut-skeleton:Thm311", "Theorem311 Source* assembly + iut-pre-stage4"),
    ("H5 O(-)^{-1} normalization", "NAMED", "e-deep:E2.h5Gap", "Mzk1HullEInputsActual / Hull09H5GapsActual"),
    ("H7 Ob9 arbitrary iterate", "NAMED", "e-deep:E3.deepOb9", "Hull13 comparison consumer / both-sided base"),
    ("EtTh deep rows", "NAMED", "e-deep:E4.etthGap", "EtTh11 rows 5-7 / EtTh02 inputs"),
    ("Frey/conductor arithmetic", "NAMED", "mainline:frey-odd-reduction", "FreyOddReduction/Conductor* tree") ]

theorem paperInputIndex_length : paperInputIndex.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperInputIndexActual