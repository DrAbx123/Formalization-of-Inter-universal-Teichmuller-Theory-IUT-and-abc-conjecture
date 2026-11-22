import tmp.sheaf.xif.paper.S3135FinalAssemblyGateV3Actual

/-!
# GATE-HYPOTHESIS AUDIT (task-62): hypotheses of the final conditional theorems vs registry

**Audit record, not a paper object.**  Mechanical mapping of the hypotheses of the
strongest conditional theorems to the registry residual ids; no deep proof is claimed.

## Theorems audited

* `S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3`
  (and its tightness `s3135_finalAssemblyGateV3_tight`);
* `S3135FinalAssemblyGateActual.s3135_finalAssemblyGate`
  (and tightness `s3135_finalAssemblyGate_tight`; gate v2/v3 are definitional wrappers).

Both theorems have the SAME hypothesis set (v3 only upgrades provenance):

1. carrier data `(I₀, v₀, R₀, n₀, D₀)` — actual paper-level carrier parameters
   (OriginalInput, source image realization, theta-pilot carrier, unit-region Haar data);
2. `hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀` — F4 card (1) / F4 (a);
3. `hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀` — F4 card (2) / F4 (b);
4. `hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)` —
   F5 card P, exactly ABC-strength.

## Registry mapping (checked against the recorded INDEX / manifest entries)

| hypothesis | registry node | citable record | exact missing |
|---|---|---|---|
| `hpt` | F4.a (value-group half) | S3135ValueGroupIdentificationActual, S3135ValueGroupDegreeUnconditionalActual | `S3135ValueMonoidIdentification` |
| `hzero` | F4.b: F4.b1 (modulus), F4.b2 (unit self-similarity), F4.b3 (paper lambda log-degree 0) | S3135HaarPushforwardActual, S3135HaarIndexActual (b1 halves); S3135LogShellUnitSelfSimilarityMissingActual (b2); S3135ScalingNormalizationActual (b3 reduction) | `S3135AdditiveHaarModulusLaw`/`S3135HaarUniquenessScalarStep`/`S3135LogShellScalingIndex` (b1), `S3135LogShellUnitSelfSimilarity` (b2), `S3135ScalingLogDegreeZero` (b3) |
| `hP` | F4.c.cardP = F5 card P | S3135F5ActualReductionActual, S3135FinalResidualActual, S3135TightnessActual | `ABCHeightWeightAdditiveBoundV2` (exactly ABC-strength by tightness) |

## Consistency checks

* **No extra hypothesis**: every hypothesis of both gate theorems is one of
  `hpt, hzero, hP` above (plus carrier data); there is no hidden assumption: the
  gate theorems are direct compositions of
  `s3135_abcConjecture_of_threeResiduals` (proved from the same three cards).
* **No unused hypothesis**: `hpt` and `hzero` are both used by the tightness theorem
  `s3135_pointWeightCard_iff_abcConjecture` (card P <=> ABC under them), and `hP` is
  used by the gate; none can be dropped without changing the statement.
* **No missing registry residual**: the registry residual set recorded in
  `s3135FinalAssemblyGateV3Report` is exactly {F4.a, F4.b (b1+b2+b3), F4.c.cardP}
  (plus the independent hull Theta-half handoff which is NOT a hypothesis of the
  F4/F5 => ABC implication, and the mainline/shehdd inputs consumed internally).
  The hypothesis set therefore covers every residual reachable through this gate.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
open LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual
open LeanFormal.IUT.XiFPaper.S3135TightnessActual
open LeanFormal.IUT.XiFPaper.S3135FinalResidualActual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV2Actual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual

namespace LeanFormal.IUT.XiFPaper.S3135GateHypothesisAuditActual

/-- One audited gate hypothesis with its registry mapping. -/
structure S3135GateHypothesisEntry where
  hypothesis : String
  registryNode : String
  citableRecord : String
  exactMissing : String
deriving Repr

/-- Hypothesis audit for the final assembly gate (v1/v2/v3 all share this set). -/
def s3135GateHypothesisTable : List S3135GateHypothesisEntry :=
  [ { hypothesis := "hpt : S3135PointLogShellFaithfulness"
      registryNode := "F4.a (value-group half)"
      citableRecord :=
        "S3135ValueGroupIdentificationActual; S3135ValueGroupDegreeUnconditionalActual"
      exactMissing := "S3135ValueMonoidIdentification" },
    { hypothesis := "hzero : S3135ScalingLogDegreeZero"
      registryNode := "F4.b: b1 modulus, b2 unit self-similarity, b3 paper lambda log-degree 0"
      citableRecord :=
        "S3135HaarPushforwardActual; S3135HaarIndexActual; " ++
          "S3135LogShellUnitSelfSimilarityMissingActual; S3135ScalingNormalizationActual"
      exactMissing :=
        "S3135AdditiveHaarModulusLaw / S3135HaarUniquenessScalarStep / " ++
          "S3135LogShellScalingIndex (b1); S3135LogShellUnitSelfSimilarity (b2); " ++
          "S3135ScalingLogDegreeZero (b3)" },
    { hypothesis := "hP : S3135ActualPointWeightCard (at abcSourcePoint)"
      registryNode := "F4.c.cardP = F5 card P (exactly ABC-strength by tightness)"
      citableRecord :=
        "S3135F5ActualReductionActual; S3135FinalResidualActual; S3135TightnessActual"
      exactMissing := "ABCHeightWeightAdditiveBoundV2" } ]

/-- Audit obligation: hypothesis -> registry mapping, with consistency checks. -/
def s3135GateHypothesisAudit : Audit.Obligation :=
  { id := "IUT-IV.gate-hypothesis-audit-v3"
    source :=
      "IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Proposition 5.8(ii); " ++
        "IUT III Remark 3.9.4; IUT III Proposition 3.9(i) p.115; IUT III Remark " ++
        "3.9.5(i) pp.158-159; IUT III Cor 3.12 :10324-10353; IUT IV Theorem 1.10 " ++
        ":1255-1385; IUT IV section 1 Proposition 1.4 iut4.txt:671-760; IUT IV " ++
        "section 2 :2329-2340; [GenEll] Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "GATE-HYPOTHESIS AUDIT (s3135_finalAssemblyGateV3 and " ++
        "s3135_finalAssemblyGate share the same hypothesis set): carrier data + " ++
        "hpt (F4.a) + hzero (F4.b: b1/b2/b3) + hP (F4.c.cardP = F5 card P).  No " ++
        "extra hypothesis: the gate is a direct composition of " ++
        "s3135_abcConjecture_of_threeResiduals.  No unused hypothesis: hpt and hzero " ++
        "are used by the tightness theorem card P <=> ABC, hP by the gate itself.  No " ++
        "missing registry residual reachable via this gate: residual set = " ++
        "{F4.a, F4.b(b1+b2+b3), F4.c.cardP}; hull Theta-half is an independent " ++
        "handoff (not a hypothesis of the F4/F5 => ABC implication); mainline and " ++
        "shehdd inputs are consumed inside the imported citable files (mainline " ++
        "numeric Q_C only via S778 gap, not claimed).  Audited table: " ++
        "s3135GateHypothesisTable.  F4 side of the audit loop closed without claiming " ++
        "the deep missing items."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "F4.a: S3135ValueMonoidIdentification",
        "F4.b1: S3135AdditiveHaarModulusLaw / S3135HaarUniquenessScalarStep / S3135LogShellScalingIndex",
        "F4.b2: S3135LogShellUnitSelfSimilarity",
        "F4.b3: S3135ScalingLogDegreeZero",
        "F4.c.cardP: ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135GateHypothesisTable
#check s3135GateHypothesisAudit
#check s3135_finalAssemblyGateV3
#check s3135_finalAssemblyGate

end LeanFormal.IUT.XiFPaper.S3135GateHypothesisAuditActual
end
