import tmp.sheaf.xif.paper.S3136ModelThetaTensorVolumeFiniteActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketLawsActual

/-! # Stage-4 host: review of the IUT IV Section 2-style estimate field (c)

Source anchors: IUT IV, Section 2 (region-volume vs normalized-weight
comparison); IUT III, Remark 3.9.4 and Prop. 3.9, (i), p. 115 (normalized
log-volumes); IUT III, Prop. 3.2, (ii) (compact tensor log-shell regions).

Field (c) of the estimate is the inequality
  regionVolume <= normalizedWeight  (region-volume form of the Cor312 Gap 2
estimate, e.g.
  Cor312ComparisonGapReduction.cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound).

CONSTRUCTIBLE FROM THE MOD-SIDE DATA (actual, in this stream):
* the native additive Haar family on qVFamTensorBlock completions
  (S3136NativeHaarFamilyActual.lgpNativeHaarFamily, IsAddHaarMeasure);
* finiteness of the Haar volume of any COMPACT tensor region
  (S3136ModelThetaTensorVolumeFiniteActual.lgpNativeHaarFamily_measure_lt_top_of_isCompact);
* the actual theta tensor scaled regions and hulls and the tensor compactness
  providers (ThetaTensorScaledImageActual.thetaTensorScaledRegion /
  thetaTensorHull; FinitePlaceArithmeticTensorBlocks.
  isCompact_arithmeticTensorTupleLogRegion);
* the concrete model theta packet and its log-scale laws
  (S3136ModelThetaPacketActual / _LawsActual);
* the actual normalized log-volume readout function
  (arithmeticTupleNormalizedLogVolume).

EXACT OBSTRUCTION (NOT constructible from mod-side data alone): the inequality
itself needs the ANALYTIC input: a split point bound for the theta labels and a
unit-region bound for the normalized comparison region.  These are the two
hypotheses of the Cor312 Gap 2 theorem; they are not consequences of the
Frobenioid/Haar data (and no card-P/ABC input is allowed).  The estimate is
therefore recorded here as the named exact missing analytic input, not as a
proved estimate.

STRENGTH CLASSIFICATION (IUT IV exact, binding): the (c) inequality is the
IUT-side undilated region/log-volume estimate of IUT IV, Theorem 1.10 shape
(THEOREM A / Cor 2.2 / Cor 2.3 chain, IV text lines 93, 1255, 1363-1385,
2380, 3117).  [GenEll] Thm 2.1 (GenEll text line 615) is the proved REDUCTION
(compactly bounded => general), NOT a proof of ABC and NOT the (c) estimate.
Class A (elementary, formalizable now): Prop 2.1, Cor 2.2 (i) BD-class height
equalities, Cor 2.3 reduction step.  Class B (proved in paper, formalization
target): Theorem 1.10 steps/holomorphic-hull log-volume estimate (unit-region
bound) and Steps (iii)-(v) prime-splitting/rounding estimates (split point
bound), with Cor 2.2 (ii),(iii) as consequences.  See
S3136RegionEstimateSourceClassificationActual for the 10-row table.

LABEL: review + honest obstruction; no claim.  Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136RegionVolumeEstimateReviewActual

/-- One review row: component, status, provider/obstruction. -/
structure LGPRegionVolumeReviewRow where
  component : String
  status : String
  providerOrObstruction : String

/-- The honest review rows for estimate field (c). -/
def lgpRegionVolumeEstimateReview : List LGPRegionVolumeReviewRow :=
  [ ⟨"native additive Haar family", "constructible",
      "S3136NativeHaarFamilyActual.lgpNativeHaarFamily + IsAddHaarMeasure instance"⟩,
    ⟨"compact tensor region volume finiteness", "constructible",
      "lgpNativeHaarFamily_measure_lt_top_of_isCompact (+ tensor compactness providers)"⟩,
    ⟨"theta tensor scaled regions / hulls", "constructible",
      "ThetaTensorScaledImageActual.thetaTensorScaledRegion / thetaTensorHull"⟩,
    ⟨"normalized log-volume readout", "constructible",
      "arithmeticTupleNormalizedLogVolume (with concrete model packet log-scale laws)"⟩,
    ⟨"regionVolume <= normalizedWeight inequality", "classB analytic input (IUT-side Theorem 1.10 shape)",
      "split point bound + unit-region bound (Cor312 Gap 2 hypotheses); not implied by mod-side/Haar data; no card-P input allowed"⟩ ]

/-- The review has 5 rows. -/
theorem lgpRegionVolumeEstimateReview_length :
    lgpRegionVolumeEstimateReview.length = 5 := rfl

#check lgpRegionVolumeEstimateReview
#check lgpRegionVolumeEstimateReview_length

end LeanFormal.IUT.XiFPaper.S3136RegionVolumeEstimateReviewActual