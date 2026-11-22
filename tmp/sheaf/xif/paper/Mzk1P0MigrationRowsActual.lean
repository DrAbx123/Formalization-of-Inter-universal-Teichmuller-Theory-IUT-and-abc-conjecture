/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT: P0 migration rows (old C3 -> native) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0MigrationRowsActual
structure MigrationRow where
  group : String
  oldField : String
  nativeReplacement : String
  consumer : String
  status : String
def migrationRows : List MigrationRow :=
  [ ⟨"S3137/hull-GAP (43)", "SourcePilotRegionData", "SourcePilotRegionDataL / native readout", "S3137 L readout", "MIGRATING"⟩,
    ⟨"C3 tensor (~100)", "C3.tensorBlock/region/Haar", "Mzk1C3LogShellTensorLActual / NativeTensorPacket", "tensor logVolume", "ACTUAL"⟩,
    ⟨"P7 (13)", "C3 theta-deg fields", "L tensor + canonical diag ratio", "#7", "MIGRATING"⟩,
    ⟨"B5/Ob33 (5)", "C3 q readout", "qVFamily/native q", "B5/Ob33", "TRIAGE"⟩,
    ⟨"roots/kummer", "completion NatRootSystem", "C3Roots.qCandidateRootSystem (AlgebraicClosure)", "native root core", "ACTUAL"⟩,
    ⟨"q/qUnit", "C3.q/qUnit", "qVFamily/Units.mk0", "native readout", "ACTUAL"⟩ ]
theorem migrationRows_length : migrationRows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0MigrationRowsActual
end