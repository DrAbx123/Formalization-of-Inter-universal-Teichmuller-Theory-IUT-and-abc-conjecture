import LeanFormal.IUT.Audit.Status

/-! # S3131 aggregated (c) status table (no discharge claims) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131RegionStatusTableActual

def S3131RegionStatusTable : List (String × String × String) :=
  [ ("region-volume reduction", "PROVEN IN TREE", "Cor312ComparisonGapReduction:306 cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound"),
    ("hunit (unit-region bound)", "PROVED IN TREE (degenerate calibration)", "HunitEpsilonTransferReduction:90; old S2722_hunitD with actual D0; degenerate via degree-faithful refutation :166"),
    ("hsplit (split-point bound)", "PARTIAL IN TREE", "GapReduction:409 hsplit_of_mem_unitRegion; (R1)-(R3) main estimates still class B (StepV gives only (R4))"),
    ("hptfin (point finiteness)", "PROVED IN TREE", "GapReduction:432 hptfin_of_mem_unitRegion; singleton-null"),
    ("hpoint (point bound)", "APPROVED ADDITIVE INPUT", "GapDictionaryLayer:372 cor312GapDict_sourcePointBound_of_additiveBound (do NOT use refuted old hval)"),
    ("theta slot", "REUSE WITH CardAMPL", "CertificateHullWiring:173 hull_le_theta; CardAMPLThetaBoundSupply; theta-constant identification with model packet OPEN"),
    ("carrier bridge", "EXISTS (old)", "S2586IQHullLogVolumeInstantiationActual:32 + lgpNativeIQInterface (S3136OldCarrierBridgeExistsActual); ABC-strength bridge old = conditional only"),
    ("NET (c)", "NOT DISCHARGED", "analytic inputs named: hsplit (R1)-(R3) class B + hpoint additive dictionary + theta-constant identification; no ABC-strength bridge as evidence") ]

theorem S3131RegionStatusTable_length : S3131RegionStatusTable.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.S3131RegionStatusTableActual