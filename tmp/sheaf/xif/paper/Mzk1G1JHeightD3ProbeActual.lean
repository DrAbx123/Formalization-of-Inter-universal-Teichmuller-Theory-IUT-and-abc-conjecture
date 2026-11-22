import tmp.sheaf.xif.paper.Mzk1G1QHeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1JHeightD3ProbeActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1QHeightActual
open MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

/-- Numeral-coefficient numerator over K. -/
def jNumN : MvPolynomial (Fin 2) K :=
  (256 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.X 1 ^ 2) ^ 3

/-- Numeral-coefficient denominator over K. -/
def jDenN : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 * (MvPolynomial.X 1 - MvPolynomial.X 0) ^ 2

def Q00N : MvPolynomial (Fin 2) K :=
  (-3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1)
    + (1 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)

def Q01N : MvPolynomial (Fin 2) K :=
  (256 : MvPolynomial (Fin 2) K) * ((3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (-6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (11 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (-8 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
    + (6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))

def Q10N : MvPolynomial (Fin 2) K :=
  (1 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (-3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)

def Q11N : MvPolynomial (Fin 2) K :=
  (256 : MvPolynomial (Fin 2) K) * ((6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (-8 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (11 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (-6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
    + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))

theorem probe_left :
    Q00N * jNumN + Q01N * jDenN = (256 : MvPolynomial (Fin 2) K) * MvPolynomial.X 0 ^ 10 := by
  unfold Q00N Q01N jNumN jDenN
  ring

theorem probe_right :
    Q10N * jNumN + Q11N * jDenN = (256 : MvPolynomial (Fin 2) K) * MvPolynomial.X 1 ^ 10 := by
  unfold Q10N Q11N jNumN jDenN
  ring

#print axioms probe_left
#print axioms probe_right

end LeanFormal.IUT.XiFPaper.Mzk1G1JHeightD3ProbeActual
end
