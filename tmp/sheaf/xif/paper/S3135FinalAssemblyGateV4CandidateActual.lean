import tmp.sheaf.xif.paper.S3135PaperLambdaConcreteActual
import tmp.sheaf.xif.paper.S3135FinalAssemblyGateV3Actual

/-!
# FINAL ASSEMBLY GATE v4 CANDIDATE (task-70)

**Candidate gate file, not a paper object; gate v3 untouched.**  New file for the Lead's
fresh explicit re-pin with shehdd after the registry freeze (12847).

## Residual set of gate v4 (v3 set with improved F4 (b) accounting)

* **F4.a** `hpt : S3135PointLogShellFaithfulness` — exact missing
  `S3135ValueMonoidIdentification` (unchanged);
* **F4.b** (formal card `hzero : S3135ScalingLogDegreeZero`; the residual accounting
  was split as):
  - b1: Haar-uniqueness scalar step **PROVED** (`S3135HaarUniquenessToolActual`,
    probed); index shift `S3135LogShellScalingIndex` remains an auxiliary statement,
    NOT needed for the paper-normalization input;
  - b2: **CORE PROVED** — integral-log-shell self-similarity under base-field p-adic
    unit scalars (`S3135LogShellScalarSelfSimilarityActual`);
  - paper input: `S3135CompletionBaseFieldUnitScalar` (minimal Prop, paper
    procession normalization, IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i)
    pp.158-159) — **PROVED for the concrete normalized model** (`scaling := 1`,
    `SourceUnitRegionHaarDataActual.lean:421`; z = z' = 1) with
    `mu(lambda·O) = mu(O)` by set equality;
  - the formal `hzero` remains the card the F4 clause consumes; its external
    justification is exactly the paper input above (degree form of the same
    procession normalization), flagged as the single F4 (b) paper input;
* **F4.c.cardP** `hP : S3135ActualPointWeightCard (abcSourcePoint ...)` — F5 card P,
  exactly ABC-strength by tightness (unchanged).

The theorem below is the v3 conditional theorem restated under the v4 residual
documentation (identical formal hypothesis set, so it is green by delegation); the
concrete-model instantiation path of the paper input is imported and #checked.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
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
open LeanFormal.IUT.XiFPaper.S3135PaperLambdaWiringActual
open LeanFormal.IUT.XiFPaper.S3135PaperLambdaConcreteActual

namespace LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV4CandidateActual

/-- **GATE v4 candidate theorem** (same formal hypothesis set as v3; improved F4 (b)
residual accounting: b1 proved, b2 core proved, paper input `S3135CompletionBaseField
UnitScalar` proved for the concrete normalized model). -/
theorem s3135_finalAssemblyGateV4
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_finalAssemblyGateV3 I₀ v₀ R₀ n₀ D₀ hpt hzero hP

/-- Tightness of gate v4 (card P <=> ABC under the two F4 cards). -/
theorem s3135_finalAssemblyGateV4_tight
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀) :
    S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀) ↔
      ABCConjecture :=
  s3135_finalAssemblyGateV3_tight I₀ v₀ R₀ n₀ D₀ hpt hzero

/-- **Gate v4 candidate residual ledger** with the improved F4 (b) accounting. -/
def s3135FinalAssemblyGateV4CandidateReport : Audit.Obligation :=
  { id := "IUT-IV.abc-final-assembly-gate-v4-candidate"
    source :=
      "IUT II section 1; IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] " ++
        "Proposition 5.8(ii); IUT III Remark 3.9.4; IUT III Proposition 3.9(i) " ++
        "p.115; IUT III Remark 3.9.5(i) pp.158-159; IUT III Cor 3.12 " ++
        ":10324-10353; IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 " ++
        "Proposition 1.4 iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] " ++
        "Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "GATE v4 CANDIDATE (fresh re-pin requested; v3 untouched).  Residual set: " ++
        "F4.a = hpt (exact missing S3135ValueMonoidIdentification); F4.b = hzero " ++
        "(formal card; residual accounting: b1 Haar-uniqueness scalar step PROVED, " ++
        "index S3135LogShellScalingIndex auxiliary and NOT needed for the paper " ++
        "normalization input; b2 CORE PROVED via base-field p-adic unit scalar " ++
        "self-similarity S3135LogShellScalarSelfSimilarityActual; paper input " ++
        "S3135CompletionBaseFieldUnitScalar PROVED for the concrete normalized model " ++
        "scaling := 1 (SourceUnitRegionHaarDataActual:421) with mu(lambda·O)=mu(O) by " ++
        "set equality; hzero external justification = the same paper procession " ++
        "normalization, the single flagged F4 (b) paper input); F4.c.cardP = hP " ++
        "(exactly ABC-strength by tightness).  Hypothesis set identical to v3, so the " ++
        "candidate is green by delegation; concrete-model instantiation path imported " ++
        "(s3135_concrete_scaling_unitScalar + s3135_concrete_haar_image_eq)."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "F4.a: S3135ValueMonoidIdentification",
        "F4.b paper input: S3135CompletionBaseFieldUnitScalar (concrete model proved)",
        "F4.c.cardP: ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135_finalAssemblyGateV4
#check s3135_finalAssemblyGateV4_tight
#check s3135FinalAssemblyGateV4CandidateReport
#check s3135_concrete_scaling_unitScalar
#check s3135_concrete_haar_image_eq

end LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV4CandidateActual
end
