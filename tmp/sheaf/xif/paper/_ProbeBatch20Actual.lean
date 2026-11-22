import tmp.sheaf.xif.paper.Mzk1G1FermatPiFiniteChartActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiRestrictFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiProperActual
import tmp.sheaf.xif.paper.Mzk1G1PsiGlobalActual
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual

/-
Batch 20 audit probe (lane=audit). Independent #print axioms checks.
Evidence versions (olean):
  * PiFiniteChart.isFinite_pi_of_chart0_restrict  17:17:53 (source has no own #print for this one)
  * PiFiniteChart.isFinite_pi_of_chartInf_restrict 17:17:53
  * PiFiniteChart.isFinite_pi                      17:17:53 (consumes both chart restrictions)
  * PiRestrictFinite.isFinite_pi                   17:16:42 (henry; consumed by PiProper.final)
  * PiRestrictFinite.isFinite_pi_restrict_chart0   17:16:42 (no own #print in source)
  * PiProper.fermatCurveToSpec_isProper_final      17:19:18 (G-A proper exit)
  * PsiGlobal.overlapToCurve_condition             17:00:24 (B1 step-4 glue condition)
  * ConductorCore.log_natAbs_discr_tower           17:10:03 (H-T 8.2 tower)
No sorry/admit/axiom in this probe.
-/
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteChartActual.isFinite_pi_of_chart0_restrict
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteChartActual.isFinite_pi_of_chartInf_restrict
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteChartActual.isFinite_pi
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi_restrict_chart0
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_final
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual.overlapToCurve_condition
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.log_natAbs_discr_tower
