import tmp.sheaf.xif.paper.S3135FinalAssemblyGateV3Actual

/-!
# task-52 batch: gate v3 handoff manifest

**Manifest, not a paper object.**  Records the current strongest artifact
(`S3135FinalAssemblyGateV3Actual`) and its verified cross-stream imports, so that
mainline / shehdd / hull and the Lead have one file listing the handoff points and
the exact residual set.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV2Actual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual

namespace LeanFormal.IUT.XiFPaper.S3135GateManifestActual

/-- Gate v3 handoff manifest: verified imports, final theorem, residual set. -/
def s3135GateV3Manifest : Audit.Obligation :=
  { id := "IUT-IV.abc-gate-v3-manifest"
    source :=
      "IUT II section 1; IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] " ++
        "Proposition 5.8(ii); IUT III Remark 3.9.4; IUT III Proposition 3.9(i) " ++
        "p.115; IUT III Remark 3.9.5(i) pp.158-159; IUT III Cor 3.12 " ++
        ":10324-10353; IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 " ++
        "Proposition 1.4 iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] " ++
        "Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "GATE v3 (S3135FinalAssemblyGateV3Actual): s3135_finalAssemblyGateV3 = " ++
        "[S3135PointLogShellFaithfulness + S3135ScalingLogDegreeZero + card P] => " ++
        "ABCConjecture; s3135_finalAssemblyGateV3_tight = card P <=> ABCConjecture " ++
        "under the two F4 cards.  Verified-green imports: S3135FinalAssemblyGateV2Actual, " ++
        "S3135ValueGroupDegreeUnconditionalActual, S3135FinalAssemblyGateActual, " ++
        "S3135TightnessActual, S3135ValueGroupIdentificationActual, " ++
        "S3135F5ActualReductionActual, S3135EndToEndV2Actual, mainline " ++
        "S3131CanonicalRootedQCActual (numeric Q_C only via S778 gap, not " ++
        "claimed), shehdd S3134FourthTriangleCompositionStatusActual / " ++
        "S3134MainlineRootedHFaActual, hull S3132QThetaConsumerWiringActual " ++
        "(S3132Task30ThetaHalfActual is a recompiling handoff).  Residuals: (a) " ++
        "S3135ValueMonoidIdentification (abc); (b) S3135AdditiveHaarModulusLaw + " ++
        "integralLogShell self-similarity + paper lambda log-degree 0 (abc; " ++
        "modulus-1 forcing and normalized-Haar equality proved on actual objects in " ++
        "S3135HaarNormalizationActual); (c) hull Theta-half C3-packet uniform " ++
        "comparison + normalization (hull); (d) card P = ABC-strength (tight)."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135ValueMonoidIdentification (F4 (a))",
        "S3135AdditiveHaarModulusLaw + log-shell self-similarity + paper lambda (F4 (b))",
        "Theta-half C3-packet uniform comparison + normalization (hull)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135GateV3Manifest

end LeanFormal.IUT.XiFPaper.S3135GateManifestActual
end
