import LeanFormal.IUT.Audit.Status

/-! # S3131 REPO-FIRST PRIOR-ART MAP (Lead directive §7.9) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131PriorArtMapActual

def S3131PriorArtMap : List (String × String) :=
  [ ("theater family (model route)", "prior art: LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:122 sourceHaarActualPrimeStrip, :146 Theater, :151 PrimeStripEquiv, :213 TheaterLink, :288 Theater_injective, :322 Family, :346 OriginalInput -> REUSE (proven in tree)"),
    ("Fact prime instance", "prior art: LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:25/28/29 completionRationalPrime + Fact(...Prime) -> REUSE"),
    ("paper-style comparison region (V2 field (a))", "prior art: LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:201 normalizedComparisonRegion W logShellPoint a b c := W.scaleShift '' (W.unitRegion ∪ {logShellPoint a b c}) -> REUSE/ADAPT"),
    ("hull log-volume interface", "prior art: Cor312ToABCBridgeInterface.lean:201 structure IQHullLogVolumeInterface (fields imageSet/hull/logVolume/unitRegion/scaleShift/...); calibration instance realLineHullData:521 (deliberately not paper model) -> REUSE structure, paper instance still needs data"),
    ("dictionary facts", "prior art: LeanFormal/IUT/ABCBridge/Arithmetic/RationalPointDictionary.lean:28-34 (logHeight₁ abcRationalPoint = log background); RationalPrimeSupport.lean:34-41 (arithmeticWeight = log radical) -> REUSE"),
    ("arithmeticWeight_nonneg", "prior art: Cor312ToABCBridgeInterface.lean:113 arithmeticWeight_nonneg -> REUSE (already used in our reductions)"),
    ("(a) V2 region construction", "prior art: normalizedComparisonRegion (line 201) subsumes our singleton region; our V2 region should be DEFINED as this construction -> ADAPT (new reuse file)"),
    ("(b)/(c) gap statement shapes", "prior art: Cor312EpsilonArithmeticComparison V1 (line 224) docstring names the two paper links as gaps; V2 adds point-dependent regions -> ADAPT"),
    ("theater/OriginalInput construction for model", "prior art: SourceUnitRegionHaarDataActual:346-353 OriginalInput + :374-430 sourceHaarActualImageRealization/sourceHaarActualUnitRegion/sourceHaarActualData -> REUSE for model-route M1/theater (no re-proving)"),
    ("height/log-volume bridge calibration", "prior art: realLineHullData:521 + cor312ToABCBridgeInterface_nonempty_of_abcConjecture:538 -> reference only (calibration, not paper model)") ]

theorem S3131PriorArtMap_length : S3131PriorArtMap.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.S3131PriorArtMapActual