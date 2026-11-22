import tmp.sheaf.xif.paper.S2576LocalDvrActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace S2576Consumer

open LeanFormal.IUT.XiFPaper.S2576LocalDvrActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual

#check @R_dedekind
#check @R_integrallyClosed
#check @R_not_isField
#check @rp_isDVR
#check @overIdeal
#check @overIdeal_isMaximal
#check @liesOver_overIdeal
#check @finite_localization_algebraMapSubmonoid
#check @finite_atPrime_of_primesOver_eq_singleton
#check @finite_atPrime_overIdeal
#check @dvr_isIntegrallyClosed
#check @LocalIntegrallyClosedGoal
#check @LocalDvrGoal
#check @isIntegrallyClosed_Aoc2_iff_localIntegrallyClosedGoal
#check @isIntegrallyClosed_Aoc2_of_localIntegrallyClosedGoal
#check @localIntegrallyClosedGoal_of_localDvrGoal
#check @isIntegrallyClosed_Aoc2_of_localDvrGoal
#check @remainingGoal_of_localDvrGoal

example : Module.Finite R Aoc2 := inferInstance
example : IsFractionRing Aoc2 L := inferInstance

/-- Consumer restatement: the DVR-local route closes IsIntegrallyClosed Aoc2. -/
theorem consumer_isIntegrallyClosed_of_localDvr (h : LocalDvrGoal) :
    IsIntegrallyClosed Aoc2 :=
  isIntegrallyClosed_Aoc2_of_localDvrGoal h

/-- Consumer restatement: the local integrally-closed goal closes the global goal. -/
theorem consumer_isIntegrallyClosed_of_localIC (h : LocalIntegrallyClosedGoal) :
    IsIntegrallyClosed Aoc2 :=
  isIntegrallyClosed_Aoc2_of_localIntegrallyClosedGoal h

/-- Consumer restatement: the local DVR route gives the S2570 remaining goal. -/
theorem consumer_remainingGoal_of_localDvr (h : LocalDvrGoal) :
    LeanFormal.IUT.XiFPaper.S2570FiniteEtaleNormalActual.RemainingGoal :=
  remainingGoal_of_localDvrGoal h

#print axioms consumer_isIntegrallyClosed_of_localDvr
#print axioms consumer_isIntegrallyClosed_of_localIC
#print axioms consumer_remainingGoal_of_localDvr

end S2576Consumer
