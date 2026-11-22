import tmp.sheaf.xif.paper.S3135HaarPushforwardActual

/-!
# task-56 route record: uniqueness bridge and Integers/Z_p bridge (searched 2026-11-10)

**Manifest/route record, not a paper object.**  Records the outcome of the required
searches before writing further proofs for F4 (b1)/(b2).

## (1) Haar-uniqueness measure-level bridge

Searched `Mathlib/MeasureTheory/Measure/**` for an integral-to-measure extension
lemma: there is NO general
`Measure.ext_of_integral_eq_of_hasCompactSupport` (only
`Measure.ext_of_charFun` / `ext_of_integral_char_eq` for probability measures on
complete normed spaces, `Basic.lean:246/99`, not applicable to the non-probability
Haar measure here).  What IS available: Haar regularity instances
`MeasureTheory.instInnerRegularOfIsHaarMeasureOfCompactSpace` and
`instRegularOfIsHaarMeasureOfCompactSpace` (`Measure/Haar/Unique.lean:683, 690`).
Recommended route therefore: get the scalar `C` on compactly supported continuous
functions from `integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport`
(`Haar/Unique.lean:292`), then prove `mu' = C • mu` by `Measure.ext` on the
open-compact basis: both sides are regular additive Haar measures, so equality on
compact open sets follows by approximating `1_K` from above/below by compactly
supported continuous functions and using regularity.  Status: NOT yet formalized.

## (2) Integers / Z_p bridge

Searched the repo Example36 files: the integer ring used with the actual completion is
`v.adicCompletionIntegers K`-shaped, e.g.
`Example36CompletionNormFormula.lean:217` and
`Example36CompletionIntoAlgCl.lean:188` (`x ∈ (v.adicCompletionIntegers F).units`),
`Example36CompletionEmbeddingActual.lean:232`, plus the fractional-ideal/generator
torsor dictionary in `Example36FiniteLocalDictionary.lean:358-384`.  There is no
defeq bridge to `ℤ_[p]`; the lattice-closure lemma
`integralLogShell_padicInt_mul_mem` therefore does not apply directly to units of
`Integers concreteLogShellField`.  Recommended route: use the `unitLog`
characterization (`LogShellSaturation.integralLogShell_unitLog_generation`,
`unitLog_eq_zero_iff_isOfFinOrder`) and the actual principal-unit comparison of
`Example36SourceLogKummerIdentification` to transport unit preservation of the log
shell, instead of a scalar cast.  Status: NOT yet formalized.

No sorry/axiom/toy; this file only records searched lemma locations and the revised
plans, so the next proof cycle starts from verified pointers.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135HaarPushforwardActual

namespace LeanFormal.IUT.XiFPaper.S3135Task56RouteRecordActual

/-- Route record: uniqueness bridge search + revised regularity-based plan, and
Integers/Z_p bridge search + revised unitLog/principal-unit plan. -/
def s3135Task56RouteRecord : Audit.Obligation :=
  { id := "IUT-IV.F4b.route-record-uniqueness-and-integers-bridge"
    source :=
      "IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) pp.158-159; " ++
        "IUT III Corollary 3.12 :10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "(1) UNIQUENESS: no Mathlib measure-level integral-ext bridge exists " ++
        "(searched MeasureTheory/Measure; only ext_of_charFun/ext_of_integral_char_eq " ++
        "for probability measures, Basic.lean:246/99, not applicable).  Available: " ++
        "Haar regularity instances Unique.lean:683/690.  Revised route: scalar C from " ++
        "integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport (line 292) + " ++
        "regularity + Measure.ext on compact open sets.  NOT yet formalized.  " ++
        "(2) INTEGERS/Z_p: repo completion integers are v.adicCompletionIntegers-shaped " ++
        "(Example36CompletionNormFormula.lean:217, Example36CompletionIntoAlgCl.lean:188, " ++
        "Example36CompletionEmbeddingActual.lean:232, " ++
        "Example36FiniteLocalDictionary.lean:358-384); no defeq bridge to Z_[p], so " ++
        "integralLogShell_padicInt_mul_mem does not apply directly.  Revised route: " ++
        "unitLog generation (LogShellSaturation:83) + unitLog_eq_zero_iff_isOfFinOrder + " ++
        "Example36 principal-unit comparison to transport unit preservation.  NOT yet " ++
        "formalized.  (3)/(4) scaling index and modulus law remain exact missing as " ++
        "recorded in S3135Task56ManifestActual; gate stays v3."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135HaarUniquenessScalarStep (route revised)",
        "S3135LogShellUnitSelfSimilarity (route revised)",
        "S3135LogShellScalingIndex",
        "S3135AdditiveHaarModulusLaw" ] }

#check s3135Task56RouteRecord

end LeanFormal.IUT.XiFPaper.S3135Task56RouteRecordActual
end
