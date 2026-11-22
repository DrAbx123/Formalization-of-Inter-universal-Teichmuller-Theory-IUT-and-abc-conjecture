import tmp.sheaf.xif.paper.S3135RegionRelativeObligationActual
import tmp.sheaf.xif.paper.S3135ModelRouteDocsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135RegionRelativeObligationActual
open LeanFormal.IUT.XiFPaper.S3135ModelRouteDocsActual

namespace LeanFormal.IUT.XiFPaper.S3135RouteFunctionLayerDocsActual

/-- **Function-layer prior-art map for the (b)/(c) attempts** (docs, no proofs): the
actual height/weight functions, region/hull volume functions, and the exact remaining
hypothesis for RegionRelativeToHullAndWeight. -/
def s3135RouteFunctionLayerMap : Audit.Obligation :=
  { id := "IUT-IV.route-b-c-function-layer-prior-art"
    source :=
      "IUT IV Theorem 1.10 :1255-1385; IUT IV section 2 :2329-2340; [GenEll] " ++
        "Definition 1.5; IUT IV:2367-2375; IUT III Proposition 3.9(i) p.115"
    status := Audit.VerificationStatus.interface
    note :=
      "PRIOR-ART MAP for (b)/(c). Functions: ArithmeticDivisorDegree.lean:1214/1221/" ++
        "1225/1310/1613 (heightWeight/hTerm/toricHeightWeight = actual height/weight " ++
        "function layer); IQCarrierConcreteModel:346/358/386 (hweightvol/hpoint " ++
        "concrete region/weight volume + point consumer); CardAMPLThetaBoundSupply:" ++
        "94/116 (realVolume_le/of_realVolume_le); ThetaBoundToHeightWeight.lean:67 " ++
        "heightWeightBound_of_normalizedVolumeComparison (production bridge).  " ++
        "(b) UNIFORM HEIGHT-VS-VOLUME: reduced to the (b)-shape hypothesis families " ++
        "of the production bridge, specialized to the paper height/weight functions " ++
        "in S3135HeightWeightAtPaperActual.s3135_heightWeightBound_atPaperFunctions. " ++
        "REMAINING HYPOTHESIS (exact): the two families (i) height <= (1+delta)*volume " ++
        "and (ii) volume <= (1+delta)*weight + thetaBound + D, uniformly for all ABC " ++
        "triples with an actual delta-indexed volume function (IUT IV Thm 1.10 shape).  " ++
        "(c) REGIONRELATIVETOHULLANDWEIGHT: shape def in " ++
        "S3135RegionRelativeObligationActual.S3135RegionRelativeToHullAndWeight " ++
        "(hull volume <= ofReal theta, hull volume finite, weight <= theta); the " ++
        "hull-volume half has prior art SourceImageHullVolume.sourceHullVolume_ge_" ++
        "imageVolume/_ge_normalized/_lt_top_of_scaledRegionImage and " ++
        "s3135_imageVolume_le_hullVolume (citable); REMAINING HYPOTHESIS: the " ++
        "arithmetic weight <= theta inequality plus the finite region volume, i.e. " ++
        "the IV section 2 normalization input, not derivable from R1.  No discharge " ++
        "claims; no registry edits."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "(b) uniform height-vs-volume families at paper height/weight",
        "(c) RegionRelativeToHullAndWeight remaining weight<=theta + finite region volume",
        "concreteRationalPrime = 5 identification (baseUnit=2 special case)" ] }

#check s3135RouteFunctionLayerMap
end LeanFormal.IUT.XiFPaper.S3135RouteFunctionLayerDocsActual
end
