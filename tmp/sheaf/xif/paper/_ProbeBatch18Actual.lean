/-
Batch 18 audit probe (lane=audit). Independent #print axioms checks for the
evaluation-scope items:
  * hviTable_final (no sum-gamma = 1, aggregate letters)        16:35:55 olean
  * ur_badWeightedLogP_le (s^Q aggregate bridge)                16:35:51 olean
  * urBadWeightSum_eq_invDegree (sum gamma = inverse degrees)   16:32:12 olean
  * localChartInf_preimage_localChart0 (P^1 cross-chart)        16:26:17 olean
  * piChart0_preimage_chart0 (PiPreimageFinal trivial)          16:29:26 olean
  * loc_u2_standardSmooth (R2 chart standard smooth)            16:37:59 olean
-/
import tmp.sheaf.xif.paper.Mzk1ULHviTableFinalActual
import tmp.sheaf.xif.paper.Mzk1URSmallPrimeActual
import tmp.sheaf.xif.paper.Mzk1URBadWeightSumActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageFinalActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmooth2Actual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ULHviTableFinalActual.hviTable_final
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.ur_badWeightedLogP_le
#print axioms LeanFormal.IUT.XiFPaper.Mzk1URBadWeightSumActual.urBadWeightSum_eq_invDegree
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual.localChartInf_preimage_localChart0
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageFinalActual.piChart0_preimage_chart0
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmooth2Actual.loc_u2_standardSmooth
