import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1StepXICorrectedGap2SemanticsV2Actual

/-!
# stepxi A688 final semantics status (three-state)

PROVED:
* Cor 3.12 requirement chain (v2_final_3_12);
* corrected-region Gap1 full bad support (v2_gap1);
* corrected Gap2 shape => ABC (v2_gap2);
* Gap2 shape <=> BadSumWeightBound (correctedGap2_iff_arith).

NAMED: corrected-region Gap2 shape (only remaining named input).
NOT_PROVED (not asserted): ABC => corrected Gap2; ABC gate NOT passed.
No misleading `corrected_gap2_iff_ABC` claim is used. -/

#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_final_3_12
#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap1
#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2SemanticsActual.correctedGap2_arith_equiv
