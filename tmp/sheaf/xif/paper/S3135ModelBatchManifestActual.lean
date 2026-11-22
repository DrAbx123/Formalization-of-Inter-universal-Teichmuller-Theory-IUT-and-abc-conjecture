import tmp.sheaf.xif.paper.S3135ModelUnitRegionInstanceActual
import tmp.sheaf.xif.paper.S3135ModelMuEqualityShapeActual

noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.S3135ModelBatchManifestActual

/-- **Model batch manifest**: the citable model pieces for task-72, their roles, and the
exact rows they fill in stage4's `LGPUnitRegionInterface` candidate. -/
def s3135ModelBatchManifest : Audit.Obligation :=
  { id := "IUT-III.model-wrapper-batch-manifest"
    source :=
      "IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) pp.158-159; " ++
        "IUT II section 1; [AbsTopIII] Proposition 5.8(ii); IUT III Remark 3.9.4"
    status := Audit.VerificationStatus.interface
    note :=
      "CITABLE MODEL PIECES (abc): S3135ModelSkeletonInterfaceActual " ++
        "(S3135ModelHullPoint := concreteLogShellField, S3135ModelHullHaar := sourceHullHaar, " ++
        "parameterized S3135ModelUnitRegionHaarData pair-record, frozen " ++
        "S3135ModelHaar_scaling_image_eq); S3135ModelHaarUnitMassActual (unit mass 1, " ++
        "finite); S3135ModelRegionSetEqActual (unit-scalar set equality + Haar " ++
        "invariance); S3135ModelValueUnitActual (value-unit log-degree zero from " ++
        "degree one, existence from unit-factor model); S3135ProcessionUnitDatumActual " ++
        "(corpus class-B datum: nonnegative scaling log-degree + antisymmetry gives " ++
        "S3135ScalingLogDegreeZero); S3135RealifiedIdentificationActual (corpus " ++
        "class-B realified identification closes S3135ValueGroupDegreeCompatibility " ++
        "using the citable degree identity); S3135ModelF4aTemplateActual (F4.a from " ++
        "the single realization log-degree equation); S3135ModelUnitRegionInstanceActual " ++
        "(parameterized S3135ModelUnitRegionHaarData instance with unit region = actual " ++
        "integral log-shell, degree zero); S3135ModelMuEqualityShapeActual (mu(2*O)=mu(O) " ++
        "shape on the actual Haar readout).  ROWS FILLED FOR STAGE4 " ++
        "LGPUnitRegionInterface: row 'base unit selection + scaling wrapper' -> supplied " ++
        "parametrically (valueUnit + baseUnit pair-record; nontrivial z=2 instance needs " ++
        "the small lemma that 2 is a Z_p-unit, i.e. concreteRationalPrime identification); " ++
        "row 'unit-region scaling identity mu(2*O)=mu(O)' -> filled for the CONCRETE " ++
        "COMPLETION readout (citable), NOT yet for native qVFamTensorBlock regions " ++
        "(needs completion/tensor-block identification = residual); row " ++
        "'regionVolume <= normalizedWeight' -> NOT ours, and equivalent to card P by " ++
        "tightness, so not derivable from R1 (explicit analytic residual)."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "native qVFamTensorBlock version of mu(2*O)=mu(O) (completion identification)",
        "2 is a Z_p-unit (needs concreteRationalPrime identification)",
        "regionVolume <= normalizedWeight (card-P equivalent, analytic residual)" ] }

#check s3135ModelBatchManifest
end LeanFormal.IUT.XiFPaper.S3135ModelBatchManifestActual
end
