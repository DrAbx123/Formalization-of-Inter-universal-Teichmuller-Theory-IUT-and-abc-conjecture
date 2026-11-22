import tmp.sheaf.xif.paper.S3137ModelTheaterFamilyActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: RETIRED — model theater prime-strip data (alternate encoding)

RETIRED (Lead/qpilot route decision, V = Unit reuse).  This file previously
attempted an alternate index-dependent family with Mon := Multiplicative (Int x
Int) and degree_k x = x1 + k*x2.  That encoding CONFLICTS with FPrimeStrip's
V-indexed Mon/degree fields and duplicates prior art; it is superseded by
SourceUnitRegionHaarDataActual.sourceHaarActualFamily (fully proved, injective,
index-dependent), reused for the model route.  Kept as a doc/record file so the
retirement is auditable.  No sorry/axiom.
-/

namespace LeanFormal.IUT.XiFPaper.S3137ModelTheaterPrimeStripDataActual

/-- Retirement record for the alternate theater-family encoding. -/
def S3137ModelTheaterPrimeStripDataRetirement : List (String × String) :=
  [ ("status", "RETIRED / PARKED (superseded)"),
    ("reason", "alternate Mon := Multiplicative (Int x Int) and degree_k encoding conflicts with FPrimeStrip V-indexed Mon/degree; duplicated prior art"),
    ("replacement", "SourceUnitRegionHaarDataActual.sourceHaarActualFamily / sourceHaarActualPrimeStrip / sourceHaarActualTheater_injective (fully proved, reuse)"),
    ("route", "V = Unit model reuse (Lead/qpilot decision); S3133ExistingModelAdaptationActual wires in-model M1/M2b on that model"),
    ("index", "INDEX.MODEL.theater-family closed by reuse (S3137ModelTheaterFamilyReuseRecord)") ]

end LeanFormal.IUT.XiFPaper.S3137ModelTheaterPrimeStripDataActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: retirement of alternate theater-family encoding. -/
def S3137ModelTheaterPrimeStripDataRetirementRecord : Obligation :=
  { id := "INDEX.MODEL.theater-family-retirement"
    source := "Lead/qpilot route decision; S3133ExistingModelAdaptationActual; SourceUnitRegionHaarDataActual"
    status := VerificationStatus.interface
    note := "RETIRED: the alternate Sum(Fin1)(Fin1) / Multiplicative(IntxInt) degree encoding is superseded by the tree family (SourceUnitRegionHaarDataActual.sourceHaarActualFamily). Model theater-family input is CLOSED BY REUSE; V = Unit route adopted; in-model M1/M2b wired by qpilot S3133ExistingModelAdaptationActual. Doc/record only."
    dependsOn := ["S3137ModelTheaterFamilyReuseRecord"] }

end LeanFormal.IUT.Audit
