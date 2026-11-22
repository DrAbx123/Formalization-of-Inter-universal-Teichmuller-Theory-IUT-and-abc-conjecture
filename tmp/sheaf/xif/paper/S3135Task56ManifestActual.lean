import tmp.sheaf.xif.paper.S3135HaarPushforwardActual

/-!
# task-56 manifest: F4 (b1)/(b2)/(b3) exact-missing status and routes

**Manifest, not a paper object.**  Single registry-facing record of the F4 (b)
subdivision after the task-56 revive of `S3135HaarPushforwardActual`.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135HaarPushforwardActual

namespace LeanFormal.IUT.XiFPaper.S3135Task56ManifestActual

/-- F4 (b) component-chain manifest for the registry. -/
def s3135Task56Manifest : Audit.Obligation :=
  { id := "IUT-IV.F4b-component-chain-manifest"
    source :=
      "IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) pp.158-159; " ++
        "IUT III Corollary 3.12 :10324-10353; IUT IV section 1 Proposition 1.4 " ++
        "iut4.txt:671-760"
    status := Audit.VerificationStatus.interface
    note :=
      "F4 (b) SUBDIVISION (registry): b1 = S3135AdditiveHaarModulusLaw, split into " ++
        "(i) pushforward half LANDED+citable S3135HaarPushforwardActual " ++
        "(mulAddEquiv, s3135_pushforward_isAddHaar) and its exact missing " ++
        "S3135HaarUniquenessScalarStep (route: integral_isAddLeftInvariant_eq_smul_of_" ++
        "hasCompactSupport Haar/Unique.lean:292 + Measure.ext; addHaarScalarFactor_smul " ++
        ":323 is NOT uniqueness), and (ii) index side LANDED+citable " ++
        "S3135HaarIndexActual (mu(integralLogShell) = logShellIntegerIndex * " ++
        "mu(Integers), Integers mass positive finite, unit mass 1) with exact missing " ++
        "S3135LogShellScalingIndex; b2 = S3135LogShellUnitSelfSimilarity " ++
        "exact missing (citable record, cast bridge Integers/Z_p pending); b3 = " ++
        "S3135ScalingLogDegreeZero (paper lambda log-degree 0, degree side).  " ++
        "Reduction landed elsewhere: (b1)+(b2) force the modulus to 1 and give " ++
        "mu(lambda·O)=mu(O) (S3135HaarNormalizationActual / " ++
        "S3135HaarNormalizedRegionActual).  None of b1,b2,b3 is ABC-strength.  " ++
        "Gate remains v3; residual (b) not dropped.  Owner: abc."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135HaarUniquenessScalarStep (b1)",
        "S3135LogShellScalingIndex (b1)",
        "S3135AdditiveHaarModulusLaw (b1)",
        "S3135LogShellUnitSelfSimilarity (b2)",
        "S3135ScalingLogDegreeZero (b3)" ] }

#check s3135Task56Manifest

end LeanFormal.IUT.XiFPaper.S3135Task56ManifestActual
end
