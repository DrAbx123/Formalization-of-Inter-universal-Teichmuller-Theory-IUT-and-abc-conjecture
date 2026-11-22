/- Probe (read-only): round-4 axiom audit, part 2 (grace + corrected andrew names). -/
import tmp.sheaf.xif.paper.Mzk1G1A3ChartDiffActual
import tmp.sheaf.xif.paper.Mzk1G1A3ChartDiffCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1A3FunctionFieldFinalActual
import tmp.sheaf.xif.paper.Mzk1HTF5StageAActual
import tmp.sheaf.xif.paper.Mzk1ULHcondAssemblyActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreSupportDataActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreDiscSupportActual

open LeanFormal.IUT.XiFPaper

-- grace: A3 chart differential / criterion / function field
#print axioms Mzk1G1A3ChartDiffActual.D_chartX_eq
#print axioms Mzk1G1A3ChartDiffActual.D_psiChart0Coord
#print axioms Mzk1G1A3ChartDiffActual.Psi_D_psiChart0Coord
#print axioms Mzk1G1A3ChartDiffCriterionActual.mem_smul_top_iff
#print axioms Mzk1G1A3ChartDiffCriterionActual.mem_smul_top_iff_Psi
#print axioms Mzk1G1A3FunctionFieldFinalActual.curve_locallyNoetherian
#print axioms Mzk1G1A3FunctionFieldFinalActual.curve_irreducibleSpace
#print axioms Mzk1G1A3FunctionFieldFinalActual.isFractionRing_chart0_functionField

-- andrew: HTF5 stage A
#print axioms Mzk1HTF5StageAActual.f5_to_f6_core
#print axioms Mzk1HTF5StageAActual.f5_to_f6_core_choice

-- sophie: hcond assembly / Legendre support
#print axioms Mzk1ULHcondAssemblyActual.hcond_of_legendreTpdSupport
#print axioms Mzk1ULHcondAssemblyActual.tripodalDictionaryOfLegendreSupport
#print axioms Mzk1ULLegendreSupportDataActual.legendreSupportIncl
#print axioms Mzk1ULLegendreSupportDataActual.legendre_tpd_subset_point
#print axioms Mzk1ULLegendreDiscSupportActual.legendre_disc_primeFactors_subset
