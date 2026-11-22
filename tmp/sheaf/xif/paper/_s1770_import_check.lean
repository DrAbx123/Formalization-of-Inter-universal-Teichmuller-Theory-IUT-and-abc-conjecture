import S1770FiniteEtaleFixedPointsActual

open CategoryTheory

-- The delivered instance, at the exact shape required by PreGaloisCategory.
#check @S1770.FiniteEtaleAlg.hasQuotientsByFiniteGroups
#check @S1770.hasQuotientsByFiniteGroupsField_holds
#check @S1770.invariantsIsLimit
#check @S1770.quotientMap
#check @S1770.existsUnique_lift_fixedSubalgebra
#print axioms S1770.hasQuotientsByFiniteGroupsField_holds
