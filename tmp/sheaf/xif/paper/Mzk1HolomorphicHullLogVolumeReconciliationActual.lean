/-! # A826 reconciliation: `HolomorphicHull` / `logVolumeComparison` obligations

Reconciliation of the `WallObligation` cards in `StepXI/Contract.lean` against
the current green assets.  The obligations are recorded as an enum, but
`StepXIContract` has no fields carrying evidence for them; the S3137 assembly
only consumes the comparison as a hypothesis.  This file records the exact
matrix; no obligation is claimed discharged unless stated. -/

structure HullLogReconRow where
  obligation : String
  representation : String
  status : String
  evidence : String

def hullLogReconRows : List HullLogReconRow :=
  [ { obligation := "WallObligation.holomorphicHull", representation := "contract enum only; no StepXIContract field", status := "NOT-DISCHARGED at contract level", evidence := "HullDeterminantLogVolumeReduction: hull adjunction idem/mono/sInter (interface); paper carrier realization NOT proved" },
    { obligation := "WallObligation.determinantNormalization", representation := "contract enum only; no StepXIContract field", status := "INTERFACE-ONLY", evidence := "matrixLogDet_* / packetDet_* / packetLogVolume_tensorPower GREEN; (Ob3-3) source identification NOT proved; C3-S1902 transport is named-data interface only (Mzk1C3S1902BridgeActual, CONDITIONAL, not progress)" },
    { obligation := "WallObligation.logVolumeComparison", representation := "qThetaPilotLogVolumeComparison C3 P", status := "PENDING (Audit obligation)", evidence := "S3137 actual readings GREEN; comparison itself not proved" },
    { obligation := "S3137 q reading", representation := "qPilotLogVolumeReading P = -|log q| <= 0", status := "GREEN", evidence := "S3137QThetaPilotLogVolumeReadingsActual" },
    { obligation := "S3137 theta reading", representation := "thetaPilotHullLogVolumeReal = log actual Haar of hull (= actual C3 region)", status := "GREEN (raw, unnormalized)", evidence := "S3137 + HullVolumeReuse; paper normalized V not identified; conditional interface thetaRead = S1902NormalizedLog + log scale + log unit (Mzk1C3S1902BridgeActual, named data only)" },
    { obligation := "HullVolumeReuse comparison", representation := "hullVolumeReadout_comparison_iff: readout inequality iff qThetaPilotLogVolumeComparison", status := "GREEN (tautological equivalence)", evidence := "Mzk1HullVolumeReuseActual" },
    { obligation := "GapNormalization sufficient reductions", representation := "theta >= 0 (or mu(O)=1 with index representation) => comparison", status := "GREEN conditional", evidence := "Mzk1GapNormalizationActual; explicitly NOT paper normalization" },
    { obligation := "S3137 -> Cor312 assembly", representation := "contractOfS3137Comparison (h) sets target=q, ipl/she/apt=True; target_le_theta:=h", status := "GREEN conditional on h", evidence := "Mzk1Cor312S3137AssemblyActual; does not discharge the hull/det/comparison cards" },
    { obligation := "N3 SharedContainer bridge", representation := "paperGap D <-> qThetaPilotLogVolumeComparison C3 P", status := "GREEN bridge", evidence := "Mzk1N3SharedContainerBridgeShaActual" },
    { obligation := "strength upgrade", representation := "Paper312Statement C3 P <-> qThetaPilotLogVolumeComparison (definitional)", status := "GREEN shape; comparison PENDING", evidence := "Mzk1Cor312StrengthHullUpgradeActual" },
    { obligation := "HullDeterminantLogVolumeReduction", representation := "Obligation status=interface; hull/det/log-volume frozen card", status := "INTERFACE (green file)", evidence := "proves det identities, hull idem/mono, final CTheta arithmetic; NOT paper carrier IQ, (Ob3-3), multiradial comparison" },
    { obligation := "final boundary Szpiro", representation := "paperGap <-> Paper312Statement <-> qTheta comparison", status := "GREEN conditional Szpiro6", evidence := "Mzk1FinalBoundarySzpiroActual; upper volume bound and two log-volume dictionaries PENDING" } ]

def hullLogReconDischarged : List String :=
  [ "S3137 actual q/theta readings (raw, unnormalized)",
    "HullDeterminantLogVolumeReduction determinant identities",
    "HullDeterminantLogVolumeReduction hull adjunction (interface)",
    "final CTheta >= -1 arithmetic (HullDeterminantLogVolumeReduction)",
    "paperGap <-> qTheta comparison bridge (N3)",
    "conditional Cor312 assembly from qTheta comparison (S3137 assembly)" ]

def hullLogReconMissing : List String :=
  [ "general qThetaPilotLogVolumeComparison (paper normalization, NOT mu(O)=1)",
    "paper carrier IQ(S+-; n, D^vdash) realization",
    "(Ob3-3) source identification: arithmetic degree of det(x)M output = normalized log-volume",
    "multiradial production of the (xi-e)/(xi-f) comparison data",
    "theta raw Haar vs paper normalized V (factor [C3 block : Q_p] and C3-vs-D dictionary); ADDRESSABLE INTERFACE Mzk1C3S1902BridgeActual (named data, no inhabitant, not progress)",
    "StepXIContract fields/linkage for holomorphicHull/determinantNormalization/logVolumeComparison",
    "exact hull volume upper bound (V <= (1/4) l (log d + log f) + C0)" ]

theorem hullLogReconRows_length : hullLogReconRows.length = 12 := rfl
theorem hullLogReconDischarged_length : hullLogReconDischarged.length = 6 := rfl
theorem hullLogReconMissing_length : hullLogReconMissing.length = 7 := rfl

#print axioms hullLogReconRows_length
