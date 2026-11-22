import LeanFormal.IUT.Audit.Status

/-! # S3131 model-route prior-art reuse (Lead 3rd-reopen scope revision) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131ModelRoutePriorArtReuseActual

def S3131ModelRoutePriorArtReuse : List (String × String) :=
  [ ("concrete model construction", "SourceUnitRegionHaarDataActual:322 sourceHaarActualFamily, :346 sourceHaarActualOriginalInput, :374 sourceHaarActualImageRealization, :416 sourceHaarActualData -> REUSED IN TREE (task-72 = prior art reuse; only adaptation files new)"),
    ("concrete IQ carrier + comparison assembly", "IQCarrierConcreteModel.lean (carrier + 5 unconditional inputs + epsilonComparison assembly) -> REUSED"),
    ("gate-v4-I", "instantiates over sourceHaarActualOriginalInput -> existing evidence; NOT promoted"),
    ("our new citable evidence (adaptation)", "class-B lemmas S3135RealifiedIdentificationActual + S3135ProcessionUnitDatumActual; F4 by-construction S3135F4BothByConstructionActual; nontrivial scaling witness -1 (S3135ModelBaseUnitActual queued); in-model M1/M2b adapted (S3133ModelM1PlaceToModActual/S3133ModelM2bDescentActual)"),
    ("theater family", "SourceUnitRegionHaarDataActual:122-166 + :288 Theater_injective -> REUSE (no new construction)"),
    ("Fact prime instance", "FinitePlacePadicScalarStructure.lean:25-32 -> REUSE") ]

theorem S3131ModelRoutePriorArtReuse_length : S3131ModelRoutePriorArtReuse.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131ModelRoutePriorArtReuseActual