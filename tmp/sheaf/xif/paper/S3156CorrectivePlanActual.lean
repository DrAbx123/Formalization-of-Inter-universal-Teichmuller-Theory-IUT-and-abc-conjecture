import LeanFormal.IUT.Audit.Status

/-! # S3156: corrective plan for the red model-route files (repo-first)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (file, diagnosis, corrective action) rows. -/
def S3156CorrectivePlan : List (String × String × String) := [
  ("S3133ModelTheaterFamilyActual", "wrong namespace path: file namespace is LeanFormal.IUT, not the long directory path; qualified names unresolved",
   "open LeanFormal.IUT (or fully qualify LeanFormal.IUT.sourceHaarActualTheater / _Family / _Theater_injective / _OriginalInput) and REUSE the proven declarations; delete re-proved family"),
  ("S3137ModelTheaterPrimeStripDataActual", "alternate Mon := Multiplicative (Int x Int) degree encoding conflicts with FPrimeStrip's V-indexed Mon/degree fields; change-tactic failures",
   "REUSE sourceHaarActualPrimeStrip (proven, with shear-matrix index) instead of a new degree encoding; use sourceHaarActualTheater_injective for injectivity"),
  ("S3135ModelScalingPairActual", "missing Fact prime instance (synthInstanceFailed) and orphan s3135_modelScaling_baseUnit_ne_zero",
   "import/reuse completionRationalPrime_fact (FinitePlacePadicScalarStructure:28) or fact_prime_five (RationalCommonPrimeFinrank:22); open scoped NNReal/ENNReal; then rebuild the pair file"),
  ("S3135ModelBaseUnitActual", "blocked by dep S3135ModelScalingPairActual EXIT=1", "wait for dep fix; then verify baseUnit=-1 witness + mu equality instance"),
  ("S3132RootedScalingDataTrivialActual", "EXIT=1 in progress (hull rooted scaling data)", "check repetition with SourceUnitRegionHaarDataActual/rooted scaling prior art before new defs"),
  ("all new model files", "repo-first rule", "report 'prior art: file:line decl -> reuse/adapt/none' BEFORE writing; no re-proving existing results") ]

theorem S3156CorrectivePlan_length : S3156CorrectivePlan.length = 6 := rfl

/-- Corrective plan record. -/
def S3156CorrectivePlanRecord : Obligation :=
  { id := "IUT.project.model-route-corrective-plan"
    source := "Lead §7.9 directive; compile diagnostics 2026-11-10 05:03"
    status := VerificationStatus.interface
    note :=
      "CORRECTIVE PLAN: theater-family files must REUSE SourceUnitRegionHaarDataActual "
      ++ "(namespace LeanFormal.IUT): delete re-proving, fix namespace, use proven family/"
      ++ "injectivity/OriginalInput. Prime-strip alternate degree encoding: reuse "
      ++ "sourceHaarActualPrimeStrip. Scaling pair: reuse Fact prime instances. Base unit: "
      ++ "unblocked after dep fix. All model files: prior-art line first, no re-proving."
    dependsOn := [ "S3156PriorArtTheater", "S3156PriorArtFactPrime", "S3156PriorArtModelHaar" ] }

#check S3156CorrectivePlanRecord
#check S3156CorrectivePlan_length

end LeanFormal.IUT.Audit
