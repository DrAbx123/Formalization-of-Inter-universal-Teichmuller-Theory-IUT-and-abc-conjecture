import tmp.sheaf.xif.paper.S2575IndexOrderMaximalityActual

/-! Consumer probe for S2575: import the built olean and restate the exported interface. -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2570FiniteEtaleNormalActual
open LeanFormal.IUT.XiFPaper.S2575IndexOrderMaximalityActual

#check @orderIsMaximal_iff_indexIdeal_eq_top
#check @orderIsMaximal_iff_isUnit_indexMatrix
#check @isIntegrallyClosed_Aoc2_of_indexIsUnitGoal
#check @discr_indexMatrix_relation
#check @finrank_Aoc2_eq_finrank_S
#check @Aoc2_le_Ssub
#check @instModuleFreeAoc2
#check @instModuleProjectiveS

example : Module.Finite R Aoc2 := inferInstance
example : Module.Free R Aoc2 := inferInstance
example : Module.Projective R S := inferInstance
example : Module.finrank R Aoc2 = Module.finrank R S := finrank_Aoc2_eq_finrank_S

#print axioms orderIsMaximal_iff_indexIdeal_eq_top
#print axioms orderIsMaximal_iff_isUnit_indexMatrix
#print axioms isIntegrallyClosed_Aoc2_of_indexIsUnitGoal
#print axioms discr_indexMatrix_relation

end
