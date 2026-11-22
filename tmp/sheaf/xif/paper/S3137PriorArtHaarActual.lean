import LeanFormal.IUT.Audit.Status

/-! # S3137: prior-art inventory (ii) SourceImageRealization / unit-region Haar data
and (iii) Haar/log-volume/unit-region data.  Source-only references. -/

namespace LeanFormal.IUT.XiFPaper.S3137PriorArtHaarActual

/-- Prior art for Haar/log-volume/unit-region fields. -/
def S3137PriorArtHaar : List (String × String × String) :=
  [ ("unit-region Haar interface", "IQCarrierHaarData.lean:181 sourceUnitRegionHaarInterface", "REUSE: actual SourceUnitRegionHaarData from SourceImageRealization"),
    ("hull log-volume finiteness", "IQCarrierHaarData.lean:207 sourceUnitRegionHaarInterface_hull_logVolume_lt_top", "REUSE"),
    ("lower bound + finiteness", "IQCarrierHaarData.lean:215 sourceUnitRegionHaarInterface_lower_bound_and_finiteness", "REUSE"),
    ("compactness input", "IQCarrierHaarData.lean:225 sourceUnitRegionHaarData_to_compactnessInput", "REUSE"),
    ("hull finiteness from compactness+contraction", "IQCarrierHaarData.lean:251 sourceHullVolume_lt_top_of_compactnessInput_and_contraction", "REUSE"),
    ("unit scaling interface", "IQCarrierHaarData.lean:265 sourceHullUnitScalingInterface", "REUSE/ADAPT: scaling normalization layer"),
    ("Cor 3.12 conclusion from unit-region data", "IQCarrierHaarData.lean:353 sourceUnitRegionHaarData_cor312Conclusion", "REUSE"),
    ("contracted unit-region data", "SourceContractedSupplyRealization.lean:219 sourceContractedUnitRegionHaarData", "REUSE"),
    ("contracted hull interface", "SourceContractedSupplyRealization.lean:239 sourceContractedHullInterface", "REUSE"),
    ("contracted point wiring Cor312 conclusion", "SourceContractedSupplyRealization.lean:253 sourceContractedPointWiringCor312Conclusion", "REUSE"),
    ("contracted normalized q conclusion", "SourceContractedSupplyRealization.lean:273 sourceContractedNormalizedQ_cor312Conclusion", "REUSE"),
    ("contraction WLOG reduction (q<1, nonpositivity)", "SourceContractionWlogReduction.lean:130/167/192/208 sourceContractedPilotWlogReduction, sourceImageLogDegree_nonpos_of_*", "REUSE"),
    ("SourceImageRealization / concrete model carriers", "IQCarrierConcreteModel.lean, SourceImageHull.lean, SourceValueHullRealizationBridge.lean (HolomorphicHull)", "REUSE: field-level realization already built; check before new defs"),
    ("source Haar actual data (input trivialization)", "SourceUnitRegionHaarDataActual.lean:400-450 sourceHaarActualOriginalInput/data (all scaling := 1)", "ADAPT/FLAG: input-fidelity trivial scaling (A12/A13); use for model inputs only") ]

theorem S3137PriorArtHaar_length : S3137PriorArtHaar.length = 14 := rfl

end LeanFormal.IUT.XiFPaper.S3137PriorArtHaarActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: prior-art inventory (ii)+(iii). -/
def S3137PriorArtHaarRecord : Obligation :=
  { id := "INDEX.PRIOR-ART.haar-log-volume"
    source := "IQCarrierHaarData.lean; SourceContractedSupplyRealization.lean; SourceContractionWlogReduction.lean; SourceUnitRegionHaarDataActual.lean"
    status := VerificationStatus.interface
    note := "PRIOR ART (ii)+(iii): the actual SourceImageRealization/unit-region Haar interface, hull log-volume finiteness, lower bound, compactness input, scaling interface and Cor 3.12 conclusion are ALREADY PROVED in IQCarrierHaarData/SourceContractedSupplyRealization/SourceContractionWlogReduction. Model/paper-route streams should REUSE them; only the input-fidelity trivial scaling (all constructors scaling := 1) remains a flagged paper-input gap."
    dependsOn := ["S3137PriorArtHaarActual"] }

end LeanFormal.IUT.Audit
