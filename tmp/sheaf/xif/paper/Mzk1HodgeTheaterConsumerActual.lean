import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample

/-!
# Mzk1HodgeTheaterConsumerActual — consumer theorems over the concrete Gaussian Hodge
theater (tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterConsumerActual

open LeanFormal.IUT

/-- Consumer: the Gaussian Hodge theater's theta packet has q = 1/2. -/
theorem consumer_gaussianTheater_q (l : PrimeGeFive) :
    (gaussianHodgeTheater l).thetaPacket.q = (1 / 2 : ℝ) :=
  gaussianHodgeTheater_q l

/-- Consumer: in the Gaussian three-theater system source and target q agree. -/
theorem consumer_threeTheater_q (l : PrimeGeFive) :
    (gaussianThreeTheaterSystem l).source.thetaPacket.q =
      (gaussianThreeTheaterSystem l).target.thetaPacket.q :=
  gaussianThreeTheaterSystem_q l

#check consumer_gaussianTheater_q
#check consumer_threeTheater_q

end LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterConsumerActual
end
