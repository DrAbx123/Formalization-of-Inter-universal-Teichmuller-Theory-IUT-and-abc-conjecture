import Mathlib

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Laichunwing Unit E: Step V noncontainment arithmetic

Exact rational/integer identities from `05_step_v_noncontainment.txt`.
The file records the arithmetic inputs of the noncontainment argument; it
does not assert the structural noncontainment theorem itself. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LaichunwingStepVNumericActual

/-- Norm of `pi = 14164 + 5825 sqrt 5` in `Z[sqrt 5]`. -/
def normPi : Rat := 14164 ^ 2 - 5 * 5825 ^ 2

theorem normPi_eq : normPi = 30965771 := by
  norm_num [normPi]

/-- The two bad-prime coordinates and their order data. -/
def m1 : Int := 2
def m2 : Int := 12

theorem m1_eq : m1 = -(-2 : Int) := by norm_num [m1]
theorem m2_eq : m2 = -(-12 : Int) := by norm_num [m2]

/-- `e_b1 = 105/gcd(105,2) = 105`, `e_b2 = 105/gcd(105,12) = 35`. -/
def e1 : Nat := 105 / Nat.gcd 105 2
def e2 : Nat := 105 / Nat.gcd 105 12

theorem e1_eq : e1 = 105 := by norm_num [e1]
theorem e2_eq : e2 = 35 := by norm_num [e2]

/-- Local degrees `1 - 1/e`. -/
def localDegree (e : Nat) : Rat := ((e : Rat) - 1) / (e : Rat)

theorem localDegree_105 : localDegree 105 = 104 / 105 := by
  norm_num [localDegree]

theorem localDegree_35 : localDegree 35 = 34 / 35 := by
  norm_num [localDegree]

/-- The `rho` values: `m/(2l)` with `2l = 14`. -/
def rho1 : Rat := 2 / 14
def rho2 : Rat := 12 / 14

theorem rho1_eq : rho1 = 1 / 7 := by norm_num [rho1]
theorem rho2_eq : rho2 = 6 / 7 := by norm_num [rho2]

/-- `lambda = j^2 * rho2 = 9 * 6/7`. -/
def lambda : Rat := 9 * (6 / 7)
theorem lambda_eq : lambda = 54 / 7 := by norm_num [lambda]

/-- `d_I = 3 d_b1 + d_b2`. -/
def dI : Rat := 3 * (104 / 105) + 34 / 35
theorem dI_eq : dI = 138 / 35 := by norm_num [dI]

/-- `a_I = 3/e1 + 1/e2`. -/
def aI : Rat := 3 / 105 + 1 / 35
theorem aI_eq : aI = 2 / 35 := by norm_num [aI]

theorem bI_eq : -aI = -(2 / 35) := by
  norm_num [aI]

/-- The Step V bound coefficient `-lambda + d_I + 1`. -/
def boundCoeff : Rat := -lambda + dI + 1

theorem boundCoeff_eq : boundCoeff = -97 / 35 := by
  norm_num [boundCoeff, lambda, dI]

/-- The inner quantity and the resulting module exponent. -/
def inner : Rat := lambda - dI - aI
theorem inner_eq : inner = 26 / 7 := by
  norm_num [inner, lambda, dI, aI]

def moduleExponent : Rat := 3 + 2 / 35
theorem moduleExponent_eq : moduleExponent = 107 / 35 := by
  norm_num [moduleExponent]

end LeanFormal.IUT.XiFPaper.Mzk1LaichunwingStepVNumericActual

end
