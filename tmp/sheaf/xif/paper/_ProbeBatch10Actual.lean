/-
Audit lane batch 10 (2026-11-16, snapshot 13:30Z): independent axiom probe.
Run ONLY through dag/watchdog via tools/wd_add.mjs.  8 entries.
-/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiActual
import tmp.sheaf.xif.paper.Mzk1LpDifferentBoundActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothLocalizeActual
import tmp.sheaf.xif.paper.Mzk1G1JHeightBezoutActual
import tmp.sheaf.xif.paper.Mzk1LpFinitenessActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartToP1Actual

-- G-A: pi is the actual glued morphism fermatCurveScheme n -> projectiveLineGlued
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual.pi
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual.pi_ι0
-- G-K §7.2 step 3: local different bound + normalisation dictionary
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LpDifferentBoundActual.localDifferentPaperOrder_le_boundedDegree
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LpDifferentBoundActual.localDifferentOrder_eq_paperOrder_mul_ramification
-- G-A §2.4: A0 localisation identification (closes the batch-9 sorryAx gap)
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothLocalizeActual.localizeEquiv
-- L-H: integer Bezout identity for the j-map
#print axioms LeanFormal.IUT.XiFPaper.G1JHeightBezoutActual.jBezUZ
-- G-K §7.2 step 2: bounded-degree finiteness reduced to per-degree finiteness
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual.boundedDegreeFinitelyManyFields_of_fixed_degree
-- G-C/B1 first segment: psi first chart as a scheme morphism, D_+(X0) preimage
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartToP1Actual.psiChart0ToP1_preimage_basicOpen
