import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 7 (task-59 maintenance; stage4 batch-7)

New LGP sub-residual ids from stage4 batch-7, under parent `LGP.residuals`.
Data only; no residual asserted.
-/

namespace LeanFormal.IUT.Audit

/-- LGP sub-node: local O-lattice quasi-lattice compatibility.  Exact declaration:
`LGPBadLocalQuasiLatticeMissing` (S3136LGPLocalOLatticeQuasiLatticeActual;
fields unitSubgroupEmbedding, olatticeCompatibility, muQuasiLatticeCompatibility,
rhoLgpCompat).  Actual content: LGPBadLocalQuasiLattice structure per bad packet
fiber (actual O-lattice + mu_2l subgroup + theta classes + equalities) with
inhabitant lgpBadLocalQuasiLattice.  IUT III Prop 3.2(ii) 97-99, 3.4(ii) 102-103,
3.7(ii),(v) 108-112. -/
def INDEX_LGP_localQuasiLattice : Obligation :=
  { id := "INDEX.LGP.local-o-lattice-quasi-lattice"
    source := "IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.4, (ii), pp. 102-103; Proposition 3.7, (ii), (v), pp. 108-112"
    status := VerificationStatus.pending
    note := "OWNER stage4. Exact declaration: LGPBadLocalQuasiLatticeMissing (S3136LGPLocalOLatticeQuasiLatticeActual; fields unitSubgroupEmbedding, olatticeCompatibility, muQuasiLatticeCompatibility, rhoLgpCompat); actual LGPBadLocalQuasiLattice + inhabitant constructed. NOT ABC-strength. PARENT: LGP.residuals."
    dependsOn := ["LGP.residuals"] }

/-- LGP sub-node: bad-weight qpilot comparison.  Exact declaration:
`LGPBadWeightQpilotComparisonMissing` (S3136LGPBadWeightQpilotCompareActual;
fields weightFamilyAgreement, normalizationFactor, logVolumeReading).  Actual
content: lgpQpilotWeightSum, lgpQpilotBothNormalized_total (both normalized
families sum to one), lgpBadNormalizedWeight_eq_qpilot_of_weightAgreement
conditional.  IUT III Rem 3.1.1(ii)-(iv) 95-97; II Rem 2.5.1(i); III Rem 3.9.4. -/
def INDEX_LGP_badWeightQpilot : Obligation :=
  { id := "INDEX.LGP.bad-weight-qpilot-comparison"
    source := "IUT III, Remark 3.1.1, (ii)-(iv), pp. 95-97; IUT II, Remark 2.5.1, (i); IUT III, Remark 3.9.4"
    status := VerificationStatus.pending
    note := "OWNER stage4. Exact declaration: LGPBadWeightQpilotComparisonMissing (S3136LGPBadWeightQpilotCompareActual; fields weightFamilyAgreement, normalizationFactor, logVolumeReading); actual lgpQpilotWeightSum + lgpQpilotBothNormalized_total, conditional lgpBadNormalizedWeight_eq_qpilot_of_weightAgreement. NOT ABC-strength. PARENT: LGP.residuals."
    dependsOn := ["LGP.residuals"] }

/-- Part-7 canonical index. -/
def S3137CanonicalResidualIndexPart7 : List Obligation :=
  [ INDEX_LGP_localQuasiLattice, INDEX_LGP_badWeightQpilot ]

theorem S3137CanonicalResidualIndexPart7_length :
    S3137CanonicalResidualIndexPart7.length = 2 := rfl

end LeanFormal.IUT.Audit
