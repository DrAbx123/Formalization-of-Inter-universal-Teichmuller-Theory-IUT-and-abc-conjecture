import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 5 (task-59 maintenance; abc F4(b1) split)

abc's F4(b1) pushforward half is now citable (S3135HaarPushforwardActual:
`mulAddEquiv c hc`, `s3135_pushforward_isAddHaar`), so the remaining F4(b1)
missing splits into two exact missing declarations under parent
`F4.b.paper-scaling-zero`.  Data only; no residual asserted.
-/

namespace LeanFormal.IUT.Audit

/-- F4(b1) sub-node: Haar uniqueness scalar step.  Exact declaration:
`S3135HaarUniquenessScalarStep : Prop` (S3135HaarPushforwardActual); the
pushforward measure is a scalar multiple of Haar.  Correct Mathlib route:
`integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport` (Haar/Unique.lean:292)
+ `Measure.ext`; caution: `addHaarScalarFactor_smul` (Unique.lean:323) is NOT the
uniqueness lemma.  Owner: abc.  With `INDEX.F4.b1.log-shell-scaling-index`
(S3135LogShellScalingIndex, index side citable in S3135HaarIndexActual) this
yields `S3135AdditiveHaarModulusLaw`. -/
def INDEX_F4_b1_haarUniqueness : Obligation :=
  { id := "INDEX.F4.b1.haar-uniqueness-scalar-step"
    source := "IUT III, Remark 3.9.4; Proposition 3.9, (i), p. 115; Mathlib measure/Haar/Unique.lean:292"
    status := VerificationStatus.provedKernel
    note := "OWNER abc. PROVED (task-64): S3135HaarUniquenessScalarStep is a theorem now — citable S3135HaarUniquenessToolActual (EXIT0; src FDE119608ABFC1B2 / olean 8698A4A7C3BFC1A9 fresh): s3135_addHaar_eq_smul (generic tool wrapping Measure.isAddLeftInvariant_eq_smul), Application.s3135_haar_pushforward_eq_smul_actual, Application.s3135_haarUniquenessScalarStep_proved. Root cause of earlier quarantine: missing open scoped NNReal (ℝ≥0 parsed as ℝ ≥ 0). NOT ABC-strength (now proved component). PARENT: F4.b.paper-scaling-zero. Remaining F4(b1) exact missing: only INDEX.F4.b1.log-shell-scaling-index (S3135LogShellScalingIndex) => S3135AdditiveHaarModulusLaw."
    dependsOn := ["F4.b.paper-scaling-zero", "INDEX.F4.b1.additive-haar-modulus-law"] }

/-- F4(b1) sub-node: log-shell scaling index.  Exact declaration:
`S3135LogShellScalingIndex : Prop` (S3135HaarIndexActual), the index side
`mu(c * Integers) = p^(-v(c)) * mu(Integers)`, already citable. -/
def INDEX_F4_b1_scalingIndex : Obligation :=
  { id := "INDEX.F4.b1.log-shell-scaling-index"
    source := "IUT III, Remark 3.9.4; Proposition 3.9, (i), p. 115"
    status := VerificationStatus.pending
    note := "OWNER abc. Exact declaration: S3135LogShellScalingIndex : Prop (S3135HaarIndexActual; index side citable). With INDEX.F4.b1.haar-uniqueness-scalar-step yields S3135AdditiveHaarModulusLaw. NOT ABC-strength. PARENT: F4.b.paper-scaling-zero."
    dependsOn := ["F4.b.paper-scaling-zero", "INDEX.F4.b1.additive-haar-modulus-law"] }

/-- Part-5 canonical index. -/
def S3137CanonicalResidualIndexPart5 : List Obligation :=
  [ INDEX_F4_b1_haarUniqueness, INDEX_F4_b1_scalingIndex ]

theorem S3137CanonicalResidualIndexPart5_length :
    S3137CanonicalResidualIndexPart5.length = 2 := rfl

end LeanFormal.IUT.Audit