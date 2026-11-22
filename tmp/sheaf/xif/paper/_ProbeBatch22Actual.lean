import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmoothFinalActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiProperActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageClose2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmooth2Actual
import tmp.sheaf.xif.paper.Mzk1ULStepVIIIActual
import tmp.sheaf.xif.paper.Mzk1G1PsiGlobalActual

/-
Batch 22 audit probe (lane=audit). Independent #print axioms checks.
Evidence versions (olean, Get-Item at probe time):
  * CurveSmoothFinal.fermatCurveToSpec_smoothOfRelativeDimension  17:40:31 (G-A smooth exit)
  * PiProper.fermatCurveToSpec_isProper_final                     17:19:18 (G-A proper exit)
  * Close2.pi_preimage_localChartInf                              16:50:10 (t-side M-b)
  * CurveSmooth2.loc_v2_standardSmooth                            16:42:12
  * ULStepVIII.hiii_of_stepII_and_sQ                              17:39:42
  * PsiGlobal.wToPullback                                         17:47:12 (NEW DONE 17:47:13)

NOTE: ChartKbar (kbar base-change step 1) is NOT DONE as of this probe
(FAIL 17:49:06, no olean); its main theorem cannot be probed and no claim is made.
The sixth slot is used for PsiGlobal.wToPullback, the new 17:47:13 DONE.
No sorry/admit/axiom in this probe.
-/
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothFinalActual.fermatCurveToSpec_smoothOfRelativeDimension
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_final
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmooth2Actual.loc_v2_standardSmooth
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIActual.hiii_of_stepII_and_sQ
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual.wToPullback
