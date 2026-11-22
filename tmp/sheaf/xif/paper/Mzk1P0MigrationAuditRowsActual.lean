/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0MigrationAuditRowsActual
structure MigrationAuditRow where
  group : String
  files : Nat
  nativeTarget : String
  status : String
def auditRows : List MigrationAuditRow :=
  [⟨"S3137/hull-GAP", 43, "native L-side readout", "MIGRATING"⟩,
   ⟨"C3 tensor", 100, "nativeLSideBlock", "MIGRATING"⟩,
   ⟨"P7", 13, "native L/native donor", "MIGRATING"⟩,
   ⟨"B5/Ob33", 5, "badPrimeSource/NativeQDonor", "GREEN"⟩]
theorem auditRows_length : auditRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0MigrationAuditRowsActual
end
