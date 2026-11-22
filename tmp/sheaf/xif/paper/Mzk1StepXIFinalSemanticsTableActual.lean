import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1StepXICorrectedGap2TightnessV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXINatRadicalBadSumV3Actual

/-!
# stepxi final semantics table (7 explicit rows)

1. Cor 3.12 requirement chain: PROVED (v2_final_3_12).
2. corrected-region Gap1 full bad support: PROVED (v2_gap1).
3. corrected Gap2 shape => ABC: PROVED (v2_gap2 / tightness V2).
4. Gap2 shape <=> BadSumWeightBound: PROVED (correctedGap2_iff_arith).
5. corrected-region Gap2 shape: NAMED (only remaining named input).
6. ABC => corrected Gap2: NOT_PROVED (not asserted).
7. ABC gate: NOT_PASSED.
No misleading corrected_gap2_iff_ABC claim. -/

#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_final_3_12
#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap1
#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2TightnessV2Actual.correctedGap2_to_ABC_tight
