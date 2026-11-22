import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 3 (task-59; stage4 LGP additions)

New LGP sub-nodes reported by stage4 after part 2, under parent
`LGP.residuals`.  Unique `INDEX.` ids; data only; no residual asserted.  Note
the actual (non-missing) theta-mu quasi-lattice class: only the paper
label-component embedding is missing.
-/

namespace LeanFormal.IUT.Audit

/-- LGP sub-node: J_v local generator transport.  Exact declaration:
`LGPJvLocalTransportMissing` (S3136LGPJvLocalTransportActual: iqPacketEmbedding,
oLatticeCompatibility, muQuasiLattice, rhoLgpCompat).  IUT III Prop 3.2(ii)
97-99; Prop 3.7(ii),(v) 108-112. -/
def INDEX_LGP_jvLocalTransport : Obligation :=
  { id := "INDEX.LGP.jv-local-generator-transport"
    source := "IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v), pp. 108-112"
    status := VerificationStatus.pending
    note := "OWNER stage4. Exact declaration: LGPJvLocalTransportMissing (S3136LGPJvLocalTransportActual; fields iqPacketEmbedding, oLatticeCompatibility, muQuasiLattice, rhoLgpCompat). NOT ABC-strength. PARENT: LGP.residuals."
    dependsOn := ["LGP.residuals"] }

/-- LGP sub-node: global units to local units.  Exact declaration:
`LGPGlobalUnitsLocalMissing` (S3136LGPGlobalUnitsToLocalUnitsActual:
sameCIdentification, placeSelection, frobeniusCompatibility,
reciprocalImageCompatibility; consumer stepxi task-55 C2; ref III:616-620 Fig.
I.5). -/
def INDEX_LGP_globalUnitsLocal : Obligation :=
  { id := "INDEX.LGP.global-units-to-local-units"
    source := "IUT III, Figure I.5 pp. 616-620 (first-triangle C2); Proposition 3.7, (ii), (v), pp. 108-112"
    status := VerificationStatus.pending
    note := "OWNER stage4. Exact declaration: LGPGlobalUnitsLocalMissing (S3136LGPGlobalUnitsToLocalUnitsActual; fields sameCIdentification, placeSelection, frobeniusCompatibility, reciprocalImageCompatibility). NOT ABC-strength. PARENT: LGP.residuals."
    dependsOn := ["LGP.residuals"] }

/-- LGP sub-node: bad-place units.  Exact declaration:
`LGPBadPlaceUnitsMissing` (S3136LGPGlobalUnitsToBadPlaceUnitsActual:
sameCIdentification, frobeniusSplittingCompatibility,
reciprocalImageCompatibility).  IUT III Prop 3.7(ii),(v) 108-112. -/
def INDEX_LGP_badPlaceUnits : Obligation :=
  { id := "INDEX.LGP.bad-place-units"
    source := "IUT III, Proposition 3.7, (ii), (v), pp. 108-112"
    status := VerificationStatus.pending
    note := "OWNER stage4. Exact declaration: LGPBadPlaceUnitsMissing (S3136LGPGlobalUnitsToBadPlaceUnitsActual; fields sameCIdentification, frobeniusSplittingCompatibility, reciprocalImageCompatibility). NOT ABC-strength. PARENT: LGP.residuals."
    dependsOn := ["LGP.residuals"] }

/-- LGP sub-node: theta-label symmetry.  Exact declaration:
`LGPThetaLabelSymmetryMissing` (S3136LGPThetaValueSymmetryActual:
iqComponentPairing, galoisPairing, logLinkPairing, muQuasiLatticePairing).  IUT
III Prop 3.4(ii) 102-103; Prop 3.7(iii),(iv). -/
def INDEX_LGP_thetaLabelSymmetry : Obligation :=
  { id := "INDEX.LGP.theta-label-symmetry"
    source := "IUT III, Proposition 3.4, (ii), pp. 102-103; Proposition 3.7, (iii), (iv), pp. 108-112"
    status := VerificationStatus.pending
    note := "OWNER stage4. Exact declaration: LGPThetaLabelSymmetryMissing (S3136LGPThetaValueSymmetryActual; fields iqComponentPairing, galoisPairing, logLinkPairing, muQuasiLatticePairing). NOT ABC-strength. PARENT: LGP.residuals. NOTE: the theta-mu quasi-lattice class itself is ACTUAL (lgpThetaValueQuotient, lgpThetaValue_quotient_root_independent, LGPThetaMuQuasiLatticeCandidate + inhabitant); only the paper label-component embedding is missing (currently inside LGPLocalPacketIdentificationMissing.labelComponents)."
    dependsOn := ["LGP.residuals"] }

/-- Part-3 canonical index. -/
def S3137CanonicalResidualIndexPart3 : List Obligation :=
  [ INDEX_LGP_jvLocalTransport,
    INDEX_LGP_globalUnitsLocal,
    INDEX_LGP_badPlaceUnits,
    INDEX_LGP_thetaLabelSymmetry ]

theorem S3137CanonicalResidualIndexPart3_length :
    S3137CanonicalResidualIndexPart3.length = 4 := rfl

end LeanFormal.IUT.Audit
