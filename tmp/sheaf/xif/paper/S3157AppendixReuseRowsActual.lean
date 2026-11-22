import LeanFormal.IUT.Audit.Status

/-! # S3157: appendix reuse rows (to fold into acceptance appendices, doc-only)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Reuse rows for the acceptance appendices (doc-only). -/
def S3157AppendixReuseRows : List String := [
  "CardAMPLThetaBoundSupply -> hull/AMPL theta-bound assets (reuse for supply-side bounds)",
  "HunitEpsilonTransferReduction -> normalization/scaling transfer assets (reuse for unit-scaling data)",
  "IUTIV/Estimates (Section1/Section2/ArithmeticDivisorDegree/StepVProcessionAverage) -> IV estimate layer + [GenEll] reduction refs (class B formalization targets)",
  "IQCarrierConcreteModel -> concrete IQ carrier model (reuse model constructions, do not redefine)",
  "SourceUnitRegionHaarDataActual -> concrete value model + theater family + injectivity + OriginalInput (core model prior art)",
  "rule: prior-art line 'file:line decl -> reuse/adapt/none' before every new Lean file; no re-proving existing results" ]

theorem S3157AppendixReuseRows_length : S3157AppendixReuseRows.length = 6 := rfl

/-- Appendix reuse rows record. -/
def S3157AppendixReuseRowsRecord : Obligation :=
  { id := "IUT.project.appendix-reuse-rows"
    source := "Lead directive item (3); prior-art inventory"
    status := VerificationStatus.interface
    note :=
      "APPENDIX REUSE ROWS (doc-only, no re-pin): add the prior-art inventory rows to the "
      ++ "acceptance appendices when mainline's table lands; keep class labels (reuse/adapt) and "
      ++ "the no-re-proving rule."
    dependsOn := [ "S3157PriorArtInventoryRecord" ] }

#check S3157AppendixReuseRowsRecord
#check S3157AppendixReuseRows_length

end LeanFormal.IUT.Audit
