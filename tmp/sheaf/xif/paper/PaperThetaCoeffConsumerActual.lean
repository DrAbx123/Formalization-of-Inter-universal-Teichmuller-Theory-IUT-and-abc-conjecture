import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncLimitZeroActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaCoeffConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual

universe u

/-- Paper-level data for the core theta coefficient at n. -/
structure PaperThetaCoeffData (K : Type u) [Field K] (n : Int) where
  coeff : HahnSeries Int K
  coeff_eq : coeff = thetaCoeffAt K n
  value_eq : coeff =
    HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
      HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1))
  support_eq : coeff.support =
    ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int)
  support_encard : coeff.support.encard = 2
  pair_eq : coeff = thetaCoeffAt K (-n - 1)

noncomputable def paperThetaCoeffData (K : Type u) [Field K] (n : Int) :
    PaperThetaCoeffData K n where
  coeff := thetaCoeffAt K n
  coeff_eq := rfl
  value_eq := thetaCoeffAt_eq_minimal K n
  support_eq := thetaCoeffAt_support_exact_minimal K n
  support_encard := thetaCoeffAt_support_encard_minimal K n
  pair_eq := (thetaCoeffAt_pair_minimal K n).symm

@[simp] theorem paperThetaCoeffData_coeff (K : Type u) [Field K] (n : Int) :
    (paperThetaCoeffData K n).coeff = thetaCoeffAt K n := rfl

@[simp] theorem paperThetaCoeffData_value (K : Type u) [Field K] (n : Int) :
    (paperThetaCoeffData K n).coeff =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) :=
  (paperThetaCoeffData K n).value_eq

@[simp] theorem paperThetaCoeffData_support_eq (K : Type u) [Field K] (n : Int) :
    (paperThetaCoeffData K n).coeff.support =
      ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) :=
  (paperThetaCoeffData K n).support_eq

@[simp] theorem paperThetaCoeffData_support_encard (K : Type u) [Field K] (n : Int) :
    (paperThetaCoeffData K n).coeff.support.encard = 2 :=
  (paperThetaCoeffData K n).support_encard

@[simp] theorem paperThetaCoeffData_pair_eq (K : Type u) [Field K] (n : Int) :
    (paperThetaCoeffData K n).coeff = thetaCoeffAt K (-n - 1) :=
  (paperThetaCoeffData K n).pair_eq

#check paperThetaCoeffData
#check paperThetaCoeffData_value
#check paperThetaCoeffData_pair_eq

end LeanFormal.IUT.XiFPaper.PaperThetaCoeffConsumerActual

end