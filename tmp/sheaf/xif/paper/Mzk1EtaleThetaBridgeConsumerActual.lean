import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge

/-!
# Mzk1EtaleThetaBridgeConsumerActual — consumer theorems over the concrete source etale
theta bridge (tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtaleThetaBridgeConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge

/-- Consumer: the reduction map is additive. -/
theorem consumer_reduction_add (l : PrimeGeFive) (m n : ℤ) :
    reduction l (m + n) = reduction l m + reduction l n :=
  reduction_add l m n

/-- Consumer: the reduction map is zero at zero. -/
theorem consumer_reduction_zero (l : PrimeGeFive) : reduction l 0 = 0 :=
  reduction_zero l

/-- Consumer: the reduction map is surjective. -/
theorem consumer_reduction_surjective (l : PrimeGeFive) :
    Function.Surjective (reduction l) :=
  reduction_surjective l

/-- Consumer: the quotient equivalence is bijective. -/
theorem consumer_quotientEquiv_bijective (l : PrimeGeFive) :
    Function.Bijective (quotientEquiv l) :=
  quotientEquiv_bijective l

/-- Consumer: the algebraic finite theta level packet is the c-stage Kummer carrier. -/
theorem consumer_level_packet_eq_stage (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).packet =
      (algebraicFiniteThetaLevel l).cStage.localCarrier.kummer :=
  level_packet_eq_stage l

#check consumer_reduction_add
#check consumer_reduction_zero
#check consumer_reduction_surjective
#check consumer_quotientEquiv_bijective
#check consumer_level_packet_eq_stage

end LeanFormal.IUT.XiFPaper.Mzk1EtaleThetaBridgeConsumerActual
end
