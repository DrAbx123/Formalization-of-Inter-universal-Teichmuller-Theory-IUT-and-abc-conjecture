/- Independent audit probe (batch 5, lane=audit).  Snapshot 2026-11-16 00:14Z.
   Recomputed #print axioms for the current-attempt DONE targets audited in
   coord/AUDIT-ROUTE-20261116.md (batch 5).  Audit-owned file: it only reads
   compiled theorems, it does not restate or strengthen them.  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartToP1Actual
import tmp.sheaf.xif.paper.Mzk1F7TameOrderActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartInfCoverActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaActual

open LeanFormal.IUT.XiFPaper

-- G-A: real two-chart gluing instance (TwoChartGluingActual DONE 00:04:36)
#print axioms Mzk1G1FermatTwoChartGluingActual.fermatChart0ToCurve_isOpenImmersion
-- G-A: real overlap ring equivalence x <-> r (FermatOverlapActual DONE 23:54:18)
#print axioms Mzk1G1FermatOverlapActual.overlapSchemeIso
-- G-A: canonical Y_n = GlueData.glued (FermatCurveActual DONE 00:07:41)
#print axioms Mzk1G1FermatCurveActual.fermatCurveScheme_eq_glued
-- G-C: first chart of psi as a scheme morphism to P^1 (PsiChartToP1Actual DONE 00:12:00)
#print axioms Mzk1G1PsiChartToP1Actual.psiChart0ToP1
-- G-C: its zero-fiber preimage D_+(X0) = D(u) (PsiChartToP1Actual DONE 00:12:00)
#print axioms Mzk1G1PsiChartToP1Actual.psiChart0ToP1_preimage_basicOpen
-- H-T / P8-P: normalized tame different order <= 1 and contribution <= log p (DONE 00:06:50)
#print axioms Mzk1F7TameOrderActual.tame_localDifferent_contribution_le_log
-- G-C: q and r generate the unit ideal on the infinity chart (DONE 23:59:36)
#print axioms Mzk1G1PsiChartInfCoverActual.span_denom_chartR_eq_top
-- G-B: actual Kaehler derivation relation n x^(n-1) dx + n y^(n-1) dy = 0 (DONE 23:54:09)
#print axioms Mzk1G1OmegaActual.derivation_relation
