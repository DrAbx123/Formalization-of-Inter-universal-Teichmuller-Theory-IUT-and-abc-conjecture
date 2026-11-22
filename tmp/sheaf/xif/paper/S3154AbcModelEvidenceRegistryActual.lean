import LeanFormal.IUT.Audit.Status

/-! # S3154: abc model-route evidence registry (F4.a/F4.b + scaling witness)

Verified rows of abc's model-route evidence for the third-reopen audit.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (file, checker verdict, declaration count, role) rows. -/
def S3154AbcModelEvidence : List (String × String × Nat × String) := [
  ("S3135RealifiedIdentificationActual.lean", "CITABLE", 2, "class-B data S3135ValueMonoidRealifiedIdentification + s3135_compatibility_of_realifiedIdentification (F4.a)"),
  ("S3135ProcessionUnitDatumActual.lean", "CITABLE", 2, "class-B data S3135ProcessionScalingUnitDatum + s3135_procession_scaling_unit_degree_zero (F4.b, antisymmetry)"),
  ("S3135F4BothByConstructionActual.lean", "CITABLE", 1, "s3135_actualF4_of_realifiedIdent_and_processionDatum: actual F4 clause from the two class-B data"),
  ("S3135ModelUnitRegionInstanceActual.lean", "CITABLE", 2, "parametric unit-region instance (valueUnit/baseUnit/unitRegion=integralLogShell/degreeBound 0/log-degree 0)"),
  ("S3135ModelValueUnitActual.lean", "CITABLE", 2, "model value-unit log-degree-zero lemmas"),
  ("S3135ModelRegionSetEqActual.lean", "CITABLE", 2, "unit scalar action preserves integralLogShell; Haar invariance by set equality"),
  ("S3135ModelMuEqualityShapeActual.lean", "CITABLE", 1, "parametric mu scaling equality shape (z*z'=1)"),
  ("S3135ModelSkeletonInterfaceActual.lean", "CITABLE", 3, "frozen model skeleton interface incl. Haar scaling image equality"),
  ("S3135ModelHaarUnitMassActual.lean", "CITABLE", 2, "unit mass 1 / finite"),
  ("S3135ModelBatchManifestActual.lean", "CITABLE", 1, "batch manifest / stage4 row mapping") ]

theorem S3154AbcModelEvidence_length : S3154AbcModelEvidence.length = 10 := rfl

/-- abc model evidence registry record. -/
def S3154AbcModelEvidenceRegistry : Obligation :=
  { id := "IUT.project.abc-model-route-evidence-registry"
    source := "abc model-route note 2026-11-10 04:55; xif_citable_check + status scan"
    status := VerificationStatus.interface
    note :=
      "TEN abc model-route evidence files verified CITABLE with real declarations (probes from "
      ++ "abc batches: trio-only where checked). Covers: F4.a class-B data lemma, F4.b class-B "
      ++ "unit datum, F4 both-by-construction theorem, parametric unit-region instance, "
      ++ "value-unit log-degree-zero, region set equality, mu equality shape, skeleton interface, "
      ++ "Haar unit mass, batch manifest. Pending: S3135ModelBaseUnitActual (baseUnit=-1 nontrivial "
      ++ "scaling witness) still compiling — verify on green (expected 4 declarations)."
    dependsOn :=
      [ "S3135F4BothByConstructionActual", "S3135RealifiedIdentificationActual",
        "S3135ProcessionUnitDatumActual", "S3135ModelUnitRegionInstanceActual" ] }

#check S3154AbcModelEvidenceRegistry
#check S3154AbcModelEvidence_length

end LeanFormal.IUT.Audit
