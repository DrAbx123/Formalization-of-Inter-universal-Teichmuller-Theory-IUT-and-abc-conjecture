import tmp.sheaf.xif.paper.PaperThetaCoeffConsumerActual
import tmp.sheaf.xif.paper.PaperQZeroLimitConsumerActual
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaInitialThetaConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual
open LeanFormal.IUT.XiFPaper.PaperThetaCoeffConsumerActual
open LeanFormal.IUT.XiFPaper.PaperQZeroLimitConsumerActual

universe u

variable {l : PrimeGeFive}

/-- Paper theta coefficient specialized to the actual InitialTheta arithmetic field K. -/
abbrev InitialThetaCoeffData (T : InitialThetaArithmeticData l) (n : Int) :=
  PaperThetaCoeffData T.K n

noncomputable def initialThetaCoeffData (T : InitialThetaArithmeticData l) (n : Int) :
    InitialThetaCoeffData T n :=
  paperThetaCoeffData T.K n

@[simp] theorem initialThetaCoeffData_coeff (T : InitialThetaArithmeticData l) (n : Int) :
    (initialThetaCoeffData T n).coeff = thetaCoeffAt T.K n := rfl

@[simp] theorem initialThetaCoeffData_value (T : InitialThetaArithmeticData l) (n : Int) :
    (initialThetaCoeffData T n).coeff =
      HahnSeries.single (thetaUExponent n) ((-1 : T.K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : T.K) ^ (-n - 1)) :=
  (initialThetaCoeffData T n).value_eq

@[simp] theorem initialThetaCoeffData_support_eq
    (T : InitialThetaArithmeticData l) (n : Int) :
    (initialThetaCoeffData T n).coeff.support =
      ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) :=
  (initialThetaCoeffData T n).support_eq

@[simp] theorem initialThetaCoeffData_support_encard
    (T : InitialThetaArithmeticData l) (n : Int) :
    (initialThetaCoeffData T n).coeff.support.encard = 2 :=
  (initialThetaCoeffData T n).support_encard

@[simp] theorem initialThetaCoeffData_pair (T : InitialThetaArithmeticData l) (n : Int) :
    (initialThetaCoeffData T n).coeff = thetaCoeffAt T.K (-n - 1) :=
  (initialThetaCoeffData T n).pair_eq

/-- Paper q^0 limit data specialized to the actual InitialTheta arithmetic field K. -/
abbrev InitialThetaQZeroData (T : InitialThetaArithmeticData l) :=
  PaperQZeroLimitData T.K

noncomputable def initialThetaQZeroData (T : InitialThetaArithmeticData l) :
    InitialThetaQZeroData T :=
  paperQZeroLimitData T.K

@[simp] theorem initialThetaQZeroData_value (T : InitialThetaArithmeticData l) :
    (initialThetaQZeroData T).coeff =
      HahnSeries.single (thetaUExponent 0) (1 : T.K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : T.K) :=
  (initialThetaQZeroData T).value_eq

@[simp] theorem initialThetaQZeroData_support_encard
    (T : InitialThetaArithmeticData l) :
    (initialThetaQZeroData T).coeff.support.encard = 2 :=
  (initialThetaQZeroData T).support_encard

#check initialThetaCoeffData
#check initialThetaCoeffData_support_eq
#check initialThetaQZeroData

end LeanFormal.IUT.XiFPaper.PaperThetaInitialThetaConsumerActual

end