import tmp.sheaf.xif.paper.Mzk1G1TwoSectionDataActual
import tmp.sheaf.xif.paper.Mzk1G1TwoSectionPsiLocalActual
import tmp.sheaf.xif.paper.Mzk1G1QHeightActual
import tmp.sheaf.xif.paper.Mzk1G1FiniteDisjointBelyiActual

/-!
# ProbeBatch3 — independent axioms probe for the 2026-11-16 batch-3 audit
Import-only probe: recomputes the axiom sets of the key theorems of the four
new DONE files. No new mathematics is asserted here.
-/

namespace ProbeBatch3

-- TwoSectionDataActual: real divisor-level statements about s0
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual.eval_protectedToZero_eq_zero_iff
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual.rootMultiplicity_protectedToZero_of_mem
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual.protectedToZeroTwoSection
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual.not_both_mem_of_span_top

-- TwoSectionPsiLocalActual: chart morphisms + cocycle
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionPsiLocalActual.psi_no_common_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionPsiLocalActual.overlapCoord_mul_cocycle
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionPsiLocalActual.twoSectionPsiData

-- QHeightActual: definitions + the trivial degenerate-value lemmas
#print axioms LeanFormal.IUT.XiFPaper.G1QHeightActual.lambdaHeight_nonneg
#print axioms LeanFormal.IUT.XiFPaper.G1QHeightActual.legendreJ_zero
#print axioms LeanFormal.IUT.XiFPaper.G1QHeightActual.legendreJ_of_rat

-- FiniteDisjointBelyiActual: only closedness of the boundary set is proved
#print axioms LeanFormal.IUT.XiFPaper.G1FiniteDisjointBelyiActual.boundarySet_isClosed

end ProbeBatch3
