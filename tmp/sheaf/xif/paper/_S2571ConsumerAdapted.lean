import tmp.sheaf.xif.paper.S2571DiscriminantPrimitiveActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2571Consumer

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2570FiniteEtaleNormalActual
open LeanFormal.IUT.XiFPaper.S2571DiscriminantPrimitiveActual

-- the exported instances really synthesize from an importing file
example : IsFractionRing R ℚ := inferInstance
example : IsIntegrallyClosed R := inferInstance
example : Algebra R ℚ := inferInstance
example : Algebra.IsSeparable ℚ L := inferInstance
example : IsFractionRing Aoc2 L := inferInstance
example : Module.Finite R Aoc2 := inferInstance

-- the exported conditional interface
#check @S_le_Aoc2_of_hypothesis
#check @isIntegrallyClosed_Aoc2_of_hypothesis
#check @S_le_Aoc2_of_model
#check @DiscrPrimitiveHypothesis
#check @ModelDiscrHypothesis

#print axioms isIntegrallyClosed_Aoc2_of_hypothesis

end LeanFormal.IUT.XiFPaper.S2571Consumer
