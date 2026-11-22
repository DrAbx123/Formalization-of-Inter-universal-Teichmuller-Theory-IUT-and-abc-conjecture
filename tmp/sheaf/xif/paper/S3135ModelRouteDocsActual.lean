import tmp.sheaf.xif.paper.S3135ModelSkeletonInterfaceActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelRouteDocsActual

/-- **Option-B evidence list + model-route documentation** (docs only; no proofs). -/
def s3135ModelRouteOptionBEvidence : Audit.Obligation :=
  { id := "IUT-IV.model-route-optionB-evidence-list"
    source :=
      "IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) pp.158-159; " ++
        "IUT III Remark 3.9.4(iv); IUT II section 1; [AbsTopIII] Proposition 5.8(ii)"
    status := Audit.VerificationStatus.interface
    note :=
      "OPTION-B EVIDENCE (all checker-CITABLE): two named class-B data lemmas -- " ++
        "S3135ValueMonoidRealifiedIdentification + s3135_compatibility_of_realifiedIdentification " ++
        "(S3135RealifiedIdentificationActual) and S3135ProcessionScalingUnitDatum + " ++
        "s3135_procession_scaling_unit_degree_zero (S3135ProcessionUnitDatumActual); " ++
        "F4 clause by construction s3135_actualF4_of_realifiedIdent_and_processionDatum " ++
        "(S3135F4BothByConstructionActual); nontrivial scaling witness " ++
        "s3135_modelBaseUnit = -1 + s3135_modelBaseUnit_norm_one + s3135_zp_negOne_mul + " ++
        "s3135_modelHaar_negOne_scaling_eq (in S3135ModelSkeletonInterfaceActual, " ++
        "probe S3135ModelBaseUnitProbeActual trio-only); parametric unit-region instance " ++
        "s3135_modelUnitRegionData (S3135ModelUnitRegionInstanceActual); scaling value " ++
        "log-degree zero (S3135ModelValueUnitActual); region preservation " ++
        "(S3135ModelRegionSetEqActual); mu-equality shape (S3135ModelMuEqualityShapeActual); " ++
        "unit mass 1 + finiteness (S3135ModelHaarUnitMassActual); batch manifest " ++
        "(S3135ModelBatchManifestActual); scaling pair record (S3135ModelScalingPairActual, " ++
        "generic over p); baseUnit=2 conditional special case " ++
        "(S3135ModelBaseUnitTwoConditionalActual).  SEPARATE S3135ModelBaseUnitActual is " ++
        "WITHDRAWN (GaussianField local Fact instance not exported; witness lives in the " ++
        "skeleton file instead).  A26 PRECISE RESIDUALS kept: (c) RegionRelativeToHullAndWeight " ++
        "+ finite hull/region volume (shape recorded in S3135RegionRelativeObligationActual; " ++
        "hull-volume half reused from SourceImageHullVolume); (b) uniform height-vs-volume " ++
        "comparison = production bridge heightWeightBound_of_normalizedVolumeComparison " ++
        "(reused in S3135HeightVolumeReuseActual, no new proof).  Abstract-contract wording + " ++
        "F4.c.cardP unchanged; no new paper input claimed; no registry edit from abc."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "(c) RegionRelativeToHullAndWeight + finite hull/region volume (mainline A26)",
        "(b) uniform height-vs-volume comparison (production bridge reused)",
        "concreteRationalPrime = 5 identification (baseUnit=2 special case)" ] }

#check s3135ModelRouteOptionBEvidence
end LeanFormal.IUT.XiFPaper.S3135ModelRouteDocsActual
end
