import tmp.sheaf.xif.paper.S2132FrobCycleActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual

#check @S2132PairCycle_exists
#check @S2132PairCycle_cycleType
#check @S2132FrobInducesPairCycleType
#check @S2132FrobInducesRootCycleType
#check @S2132FrobInduces_iff
#check @S2132Bridge_of_factorization
#check @S2132Bridge_of_factorization_and_honest
#check @S2132Psi5Remaining_of_factorization
#check @S2132ImageTail_of_cycleType_and_transitive
#check @S2132D5LargeImageFive_of_rangeHypotheses
#check @S2132D5LargeImageFive_of_rangeData
#check @S2132FirstMissing
#check @S2132Remaining_of_honest_and_factorization
#check @S2132CorrectedProduct
#check @S2132RecordedProduct_false
#check @S2132Psi5Q_eval_zero
#check @S2132NoIntegerModel
#check @S2132Mod29FactorizationData_empty
#check @S2132S2041Psi5Remaining_false

example : ∃ ρ : Equiv.Perm S2056Pair, ρ.cycleType = ({2, 10} : Multiset Nat) :=
  S2132PairCycle_exists

#print axioms S2132PairCycle_cycleType
#print axioms S2132FrobInduces_iff
#print axioms S2132ImageTail_of_cycleType_and_transitive
#print axioms S2132D5LargeImageFive_of_rangeHypotheses
#print axioms S2132Bridge_of_factorization_and_honest
#print axioms S2132Psi5Remaining_of_factorization
#print axioms S2132Remaining_of_honest_and_factorization
#print axioms S2132RecordedProduct_false
#print axioms S2132NoIntegerModel
#print axioms S2132Mod29FactorizationData_empty
#print axioms S2132S2041Psi5Remaining_false

end
