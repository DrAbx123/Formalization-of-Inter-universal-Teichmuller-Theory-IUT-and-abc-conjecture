import LeanFormal.IUT.Audit.Status

/-! # S3159: base-unit fix guidance (last Option-B blocker)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Guidance rows for S3135ModelBaseUnitActual. -/
def S3159BaseUnitFixGuidance : List (String × String) := [
  ("namespace of mu-equality file", "S3135ModelMuEqualityShapeActual's namespace is LeanFormal.IUT.XiFPaper.S3135ModelBatch3Actual (import it, open that namespace; the stale 'unknown namespace S3135ModelMuEqualityShapeActual' errors are from an older revision)"),
  ("Fact instance", "local instance factBaseCRP : Fact (Nat.Prime concreteRationalPrime) := completionRationalPrime_fact concretePlace is already present; ensure it is BEFORE any Q_[concreteRationalPrime] use and that concretePlace is imported (ConcreteSourceFrobenioidBridge)"),
  ("duplicate opens", "remove duplicate open S3135ModelBatch3Actual lines (22/25) and re-run; remaining synthInstanceFailed likely resolves once namespace/Fact are in scope"),
  ("witness content", "s3135_modelBaseUnit (-1 : Q_[crp])^x with inv=-1, product=1, norm_one; then mu((-1)*O)=mu(O) instance via RegionSetEq/SkeletonInterface"),
  ("verification", "after green: checker + probe + declaration audit; then Option-B certifiable") ]

theorem S3159BaseUnitFixGuidance_length : S3159BaseUnitFixGuidance.length = 5 := rfl

/-- Base-unit fix guidance record. -/
def S3159BaseUnitFixGuidanceRecord : Obligation :=
  { id := "IUT.project.base-unit-fix-guidance"
    source := "audit of S3135ModelBaseUnitActual 3349B + importers 2026-11-10 05:16"
    status := VerificationStatus.interface
    note :=
      "BASE-UNIT FIX (last Option-B blocker): correct namespace is LeanFormal.IUT.XiFPaper."
      ++ "S3135ModelBatch3Actual for the mu-equality shape; Fact instance present (completionRational"
      ++ "Prime_fact concretePlace); remove duplicate opens; then baseUnit=-1 witness + mu equality "
      ++ "instance should compile; checker+probe on green."
    dependsOn := [ "S3135ModelBaseUnitActual", "S3135ModelMuEqualityShapeActual" ] }

#check S3159BaseUnitFixGuidanceRecord
#check S3159BaseUnitFixGuidance_length

end LeanFormal.IUT.Audit
