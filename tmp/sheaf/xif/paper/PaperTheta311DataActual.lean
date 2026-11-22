import tmp.sheaf.xif.paper.PaperThetaInitialThetaConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperTheta311DataActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual
open LeanFormal.IUT.XiFPaper.PaperThetaInitialThetaConsumerActual

universe u

variable {l : PrimeGeFive}

/-- Theorem 3.11 theta-side data over the actual InitialTheta arithmetic field. -/
structure PaperTheta311ThetaData (T : InitialThetaArithmeticData l) where
  q0 : InitialThetaQZeroData T
  coeffAt : forall n : Int, InitialThetaCoeffData T n
  q0_value : q0.coeff =
    HahnSeries.single (thetaUExponent 0) (1 : T.K) +
      HahnSeries.single (thetaUExponent (-1)) (-1 : T.K)
  q0_support_encard : q0.coeff.support.encard = 2
  coeffAt_support : forall n : Int,
    (coeffAt n).coeff.support =
      ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int)

noncomputable def paperTheta311ThetaData (T : InitialThetaArithmeticData l) :
    PaperTheta311ThetaData T where
  q0 := initialThetaQZeroData T
  coeffAt := fun n => initialThetaCoeffData T n
  q0_value := initialThetaQZeroData_value T
  q0_support_encard := initialThetaQZeroData_support_encard T
  coeffAt_support := fun n => initialThetaCoeffData_support_eq T n

@[simp] theorem paperTheta311ThetaData_q0 (T : InitialThetaArithmeticData l) :
    (paperTheta311ThetaData T).q0 = initialThetaQZeroData T := rfl

theorem paperTheta311ThetaData_q0_value (T : InitialThetaArithmeticData l) :
    (paperTheta311ThetaData T).q0.coeff =
      HahnSeries.single (thetaUExponent 0) (1 : T.K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : T.K) :=
  (paperTheta311ThetaData T).q0_value

theorem paperTheta311ThetaData_coeffAt_support (T : InitialThetaArithmeticData l)
    (n : Int) :
    ((paperTheta311ThetaData T).coeffAt n).coeff.support =
      ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) :=
  (paperTheta311ThetaData T).coeffAt_support n

theorem paperTheta311ThetaData_q0_support_encard
    (T : InitialThetaArithmeticData l) :
    (paperTheta311ThetaData T).q0.coeff.support.encard = 2 :=
  (paperTheta311ThetaData T).q0_support_encard

theorem paperTheta311ThetaData_coeffAt_value
    (T : InitialThetaArithmeticData l) (n : Int) :
    ((paperTheta311ThetaData T).coeffAt n).coeff =
      HahnSeries.single (thetaUExponent n) ((-1 : T.K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : T.K) ^ (-n - 1)) :=
  ((paperTheta311ThetaData T).coeffAt n).value_eq

theorem paperTheta311ThetaData_coeffAt_pair
    (T : InitialThetaArithmeticData l) (n : Int) :
    ((paperTheta311ThetaData T).coeffAt n).coeff =
      thetaCoeffAt T.K (-n - 1) :=
  ((paperTheta311ThetaData T).coeffAt n).pair_eq

#check paperTheta311ThetaData
#check paperTheta311ThetaData_q0_value
#check paperTheta311ThetaData_coeffAt_support

end LeanFormal.IUT.XiFPaper.PaperTheta311DataActual

end