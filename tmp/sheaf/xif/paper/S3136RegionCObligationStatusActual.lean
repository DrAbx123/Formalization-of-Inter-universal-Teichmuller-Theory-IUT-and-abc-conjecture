/-! # Stage-4 host: aggregated (c) obligation status table (post-mining)

PRIOR ART (checked first; details in S3136OldAttemptHonestyAuditActual,
S3136SplitPointPriorArtExactActual, S3136PriorArtCor312SuppliesActual):
* S2586IQHullLogVolumeInstantiationActual:32 concrete IQ carrier over native Haar;
* S2722HunitDActual:44 hunit with ACTUAL D0; S2720BridgeHaarActual:70 hsplit;
  singleton-null hptfin;
* Cor312ComparisonGapReduction:306 gap2 reduction, :409/:432/:455/:525/:599 support;
* Cor312GapDictionaryLayer:34/39 directions, :368 additive point bound;
* CardAMPLThetaBoundSupply:78 theta supply; CertificateHullWiring:173/:301;
* StepVProcessionAverage:35/68/100; ElementaryEstimates:76-146 e1-e6.

CONSUMER: mainline/lattice (c) status reporting.  This data table aggregates the
post-mining status of each (c) obligation slot: WIRED / CONDITIONAL / MISSING, with
the exact producer and the exact residual input.  No discharge is claimed.

LABEL: status table (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136RegionCObligationStatusActual

structure LGPCObligationRow where
  slot : String
  status : String
  producer : String
  residual : String

def lgpCObligationStatus : List LGPCObligationRow :=
  [ ⟨"carrier bridge (measure -> IQ log-volume)", "WIRED", "S2586IQHullLogVolumeInstantiationActual:32 (logVolume := Measure.addHaar, unitRegion := canonical unit reference, hull := rootNormHull, scaleShift := id)", "degenerate point semantics: Haar singletons null"⟩,
    ⟨"unit-region bound (hunit)", "WIRED", "S2722HunitDActual:44 S2722_hunitD with actual D0 = max 0 (unitVol - hullVol); source-interface variant via HunitEpsilonTransferReduction:118 (D0 = 0) in S3136Gap2AdditiveWiringActual.lgpSourceInterface_hunit", "for the source-interface variant the datum is the degenerate sourceHaarActualData"⟩,
    ⟨"split-point bound (hsplit)", "WIRED shape", "S2720BridgeHaarActual:70 normalizedRegion_logVolume_le_split (S2586 carrier); Cor312ComparisonGapReduction:409 hsplit_of_mem_unitRegion (membership form)", "the paper's (R1)-(R3) prime-splitting estimates remain the analytic content (class B)"⟩,
    ⟨"point finiteness (hptfin)", "WIRED", "singleton-null on the S2586 carrier; Cor312ComparisonGapReduction:432 hptfin_of_mem_unitRegion", "degenerate: singleton Haar volume 0"⟩,
    ⟨"point bound (hpoint)", "CONDITIONAL", "approved additive input: Cor312GapDictionaryLayer:372 cor312GapDict_sourcePointBound_of_additiveBound (height <= (1+eps)weight + A, plus degree/height comparison hline); wired in S3136Gap2AdditiveWiringActual.lgpGap2_of_additive", "named inputs: additive height bound hadd, degree/height comparison hline, point membership hmem; NO nondegenerate producer"⟩,
    ⟨"theta upper bound", "CONDITIONAL", "CardAMPLThetaBoundSupply:78 fields + CertificateHullWiring:173 hull_le_theta slot; conditional model slot in S3136CertificateThetaSlotActual", "identification theta = model Theta log-volume needs 0 <= theta and hull bound; refutation CertificateHullWiring:301 under degree faithfulness"⟩,
    ⟨"weighted-average side", "WIRED (reuse)", "StepVProcessionAverage:35/54/68 + ElementaryEstimates:76-146 e1-e6 (reused)", "label-weight identification rows only"⟩,
    ⟨"(c) inequality regionVolume <= normalizedWeight", "CONDITIONAL", "Cor312ComparisonGapReduction:306 applied in S3136Gap2AdditiveWiringActual with hunit/hsplit/hptfin wired and hpoint from additive input", "exact remaining: hadd additive height input, hline degree/height comparison, hmem membership, nondegenerate point semantics"⟩ ]

theorem lgpCObligationStatus_length : lgpCObligationStatus.length = 8 := rfl

#check lgpCObligationStatus
#check lgpCObligationStatus_length

end LeanFormal.IUT.XiFPaper.S3136RegionCObligationStatusActual