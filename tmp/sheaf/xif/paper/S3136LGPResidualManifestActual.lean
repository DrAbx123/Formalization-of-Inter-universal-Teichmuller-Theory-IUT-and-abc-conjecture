/-! # Stage-4 host: manifest of the LGP residual sub-nodes

Data-only manifest of the canonical LGP residual sub-nodes (ids agreed with the
lattice S3137 residual index) together with the owning file, the exact Missing
record and the component status.  No paper object is claimed; every entry is a
named component record or an actual component.

Coordinated with lattice's INDEX.LGP.* ids; consumers: gate, lattice, mainline.
-/

namespace LeanFormal.IUT.XiFPaper.S3136LGPResidualManifestActual

/-- One LGP residual sub-node entry. -/
structure LGPResidualNode where
  /-- Canonical id (lattice INDEX.LGP.*). -/
  id : String
  /-- Owning file (workspace-relative). -/
  file : String
  /-- Exact Missing record name. -/
  recordName : String
  /-- Component status. -/
  status : String

/-- The manifest of LGP residual sub-nodes. -/
def lgpResidualManifest : List LGPResidualNode :=
  [ ⟨"local-tensor-packet-identification",
      "tmp/sheaf/xif/paper/S3136LGPLocalTensorPacketActual.lean",
      "LGPLocalPacketIdentificationMissing", "component-exact-missing"⟩,
    ⟨"tensor-o-lattice-identification",
      "tmp/sheaf/xif/paper/S3136LGPTensorOLatticeIdentificationActual.lean",
      "LGPTensorOLatticeIdentificationMissing", "component-exact-missing"⟩,
    ⟨"jv-packet-transport",
      "tmp/sheaf/xif/paper/S3136LGPJvPacketTransportActual.lean",
      "LGPJvPacketTransportMissing", "component-exact-missing"⟩,
    ⟨"jv-local-generator-transport",
      "tmp/sheaf/xif/paper/S3136LGPJvLocalTransportActual.lean",
      "LGPJvLocalTransportMissing", "component-exact-missing"⟩,
    ⟨"jv-q-span-embedding",
      "tmp/sheaf/xif/paper/S3136LGPJvQSpanTopActual.lean",
      "LGPJvQSpanEmbeddingMissing", "component-exact-missing"⟩,
    ⟨"realified-value-transport",
      "tmp/sheaf/xif/paper/S3136LGPRealifiedValueTransportActual.lean",
      "LGPRealifiedValueTransportMissing", "component-exact-missing"⟩,
    ⟨"qv-principal-ideal",
      "tmp/sheaf/xif/paper/S3136LGPQVPilotPrincipalIdealActual.lean",
      "LGPQVPilotPrincipalIdealMissing", "component-exact-missing"⟩,
    ⟨"local-monoid-identification",
      "tmp/sheaf/xif/paper/S3136LGPLocalMonoidActual.lean",
      "LGPLocalMonoidIdentificationMissing", "component-exact-missing"⟩,
    ⟨"xmu-unit-portion",
      "tmp/sheaf/xif/paper/S3136LGPXMuUnitActual.lean",
      "LGPXMuUnitIdentificationMissing", "component-exact-missing"⟩,
    ⟨"frobenioid-mod-to-MOD-iso",
      "tmp/sheaf/xif/paper/S3136FrobenioidIsoLayerActual.lean",
      "FrobenioidModToMODIsoMissing", "component-exact-missing"⟩,
    ⟨"frobenioid-carrier-functor",
      "tmp/sheaf/xif/paper/S3136ModSideInputActual.lean",
      "FrobenioidCarrierFunctorMissing", "component-exact-missing"⟩,
    ⟨"bad-family-packet",
      "tmp/sheaf/xif/paper/S3136LGPBadFamilyPacketActual.lean",
      "LGPBadFamilyMissing", "component-exact-missing"⟩,
    ⟨"bad-weight-normalization",
      "tmp/sheaf/xif/paper/S3136LGPBadWeightNormalizationActual.lean",
      "LGPBadWeightNormalizationMissing", "component-exact-missing"⟩,
    ⟨"bad-weight-qpilot-comparison",
      "tmp/sheaf/xif/paper/S3136LGPBadWeightQpilotCompareActual.lean",
      "LGPBadWeightQpilotComparisonMissing", "component-exact-missing"⟩,
    ⟨"local-o-lattice-quasi-lattice",
      "tmp/sheaf/xif/paper/S3136LGPLocalOLatticeQuasiLatticeActual.lean",
      "LGPBadLocalQuasiLatticeMissing", "component-exact-missing"⟩,
    ⟨"global-units-to-local-units",
      "tmp/sheaf/xif/paper/S3136LGPGlobalUnitsToLocalUnitsActual.lean",
      "LGPGlobalUnitsLocalMissing", "component-exact-missing"⟩,
    ⟨"bad-place-units",
      "tmp/sheaf/xif/paper/S3136LGPGlobalUnitsToBadPlaceUnitsActual.lean",
      "LGPBadPlaceUnitsMissing", "component-exact-missing"⟩,
    ⟨"theta-label-symmetry",
      "tmp/sheaf/xif/paper/S3136LGPThetaValueSymmetryActual.lean",
      "LGPThetaLabelSymmetryMissing", "component-exact-missing"⟩,
    ⟨"theta-class-log-channel",
      "tmp/sheaf/xif/paper/S3136LGPThetaClassLogWeightActual.lean",
      "LGPThetaClassLogChannelMissing", "component-exact-missing"⟩,
    ⟨"unit-layer-qv",
      "tmp/sheaf/xif/paper/S3136LGPThetaValueUnitLayerActual.lean",
      "LGPUnitLayerQvMissing", "component-exact-missing"⟩ ]

/-- The manifest has 20 entries. -/
theorem lgpResidualManifest_length :
    lgpResidualManifest.length = 20 := rfl

#check lgpResidualManifest
#check lgpResidualManifest_length

end LeanFormal.IUT.XiFPaper.S3136LGPResidualManifestActual