import LeanFormal.IUT.Audit.Status

/-! # S3143: no-vendor-import audit record

Static audit result: no stream file imports the vendor snapshot / its Iut.Stage*
module roots; prose mentions are honesty notes only.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Files whose vendor mentions were audited (prose-only). -/
def S3143VendorProseMentionFiles : List String := [
  "_S1405Probe3.lean",
  "S1300HDDHullDetActual.lean",
  "S1393XRepFiberBoundActual.lean",
  "S1394PsiSqZeroActual.lean" ]

theorem S3143VendorProseMentionFiles_length :
    S3143VendorProseMentionFiles.length = 4 := rfl

/-- Forbidden import roots checked by the audit (data). -/
def S3143ForbiddenVendorImportRoots : List String := [
  "import Iut.Stage1",
  "import Iut.Stage2",
  "import Iut.SourceTrace",
  "import .*vendor/promachina",
  "import .*snapshots" ]

theorem S3143ForbiddenVendorImportRoots_length :
    S3143ForbiddenVendorImportRoots.length = 5 := rfl

/-- No-vendor-import audit record. -/
def S3143VendorNoImportAudit : Obligation :=
  { id := "IUT.project.vendor-no-import-audit"
    source := "grep audit 2026-11-10 04:15 over tmp/sheaf/xif/paper + lakefile"
    status := VerificationStatus.interface
    note :=
      "AUDITED: zero imports of Iut.Stage1/Iut.Stage2/Iut.SourceTrace root modules and zero " ++
        "vendor/snapshot import paths anywhere under tmp/sheaf/xif/paper; vendor mentions are " ++
        "prose honesty notes in 4 files only. Vendor is source-reference only; no stream " ++
        "claims a vendor import."
    dependsOn := [] }

#check S3143VendorNoImportAudit
#check S3143ForbiddenVendorImportRoots_length

end LeanFormal.IUT.Audit
